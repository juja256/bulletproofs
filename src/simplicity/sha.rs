//! The transcript of a compiled verifier: [`CompileTranscript`] (a `Sha256Transcript` that keeps
//! its records) and the lowering of its records into SHA-256 jets.

use sha2::{Digest, Sha256};

use crate::simplicity::ir::{Op, Prog, Ty, Val};
use crate::simplicity::SIGHASH_LABEL;
use crate::transcript::{TranscriptBackend, TranscriptRef};
use crate::Sha256Transcript;

/// `2^256 mod n` for secp256k1: a scalar from 64 challenge bytes is `o0 · R + o1` (both reduced).
pub(crate) const R_SECP256K1: [u8; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x45, 0x51, 0x23, 0x19, 0x50, 0xb7, 0x5f, 0xc4, 0x40, 0x2d, 0xa1, 0x73,
    0x2f, 0xc9, 0xbe, 0xbf,
];

/// Where the bytes of a part of a record come from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Part {
    /// Bytes the program knows (labels, lengths, statement data).
    Const(Vec<u8>),
    /// The 32-byte message under [`SIGHASH_LABEL`]: `jet_sig_all_hash` in the program.
    Sighash,
    /// The 33-byte SEC1 encoding of the proof's point number `i` (witness).
    WitPoint(usize),
    /// The 32 bytes of a traced scalar (a node of the tape).
    Scalar(u32),
}

impl Part {
    fn len(&self) -> usize {
        match self {
            Part::Const(b) => b.len(),
            Part::Sighash | Part::Scalar(_) => 32,
            Part::WitPoint(_) => 33,
        }
    }
}

/// A record of the transcript, by provenance of its bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rec {
    /// Bytes absorbed (the tag block, an append).
    Bytes(Vec<Part>),
    /// A challenge: its request record (constant bytes) and its output length.
    Challenge {
        /// `0x43 ‖ le32(len(label)) ‖ label ‖ le32(len)`.
        request: Vec<u8>,
        /// The output length in bytes.
        len: usize,
    },
}

/// A transcript that keeps its records: the transcript a circuit is compiled with
/// ([`Verifier::compile_to_simplicity`](crate::r1cs::Verifier)). Same bytes and state as a
/// [`Sha256Transcript`] after the same operations, which it wraps; the prover uses the latter.
#[derive(Clone, Debug)]
pub struct CompileTranscript {
    inner: Sha256Transcript,
    log: Vec<Rec>,
}

fn le32(n: usize) -> [u8; 4] {
    (n as u32).to_le_bytes()
}

impl CompileTranscript {
    /// A transcript for the application `label`, as `Sha256Transcript::new`.
    pub fn new(label: &'static [u8]) -> Self {
        let t = Sha256::digest(b"bulletproofs/transcript/sha256/v1");
        let mut tag = t.to_vec();
        tag.extend_from_slice(&t);
        let mut s = CompileTranscript { inner: Sha256Transcript::new(label), log: vec![Rec::Bytes(vec![Part::Const(tag)])] };
        s.log_append(b"dom-sep", label);
        s
    }

    /// The records so far.
    pub(crate) fn log(&self) -> &[Rec] {
        &self.log
    }

    fn log_append(&mut self, label: &[u8], message: &[u8]) {
        let mut head = vec![0x41];
        head.extend_from_slice(&le32(label.len()));
        head.extend_from_slice(label);
        head.extend_from_slice(&le32(message.len()));
        let body = if label == SIGHASH_LABEL && message.len() == 32 {
            Part::Sighash
        } else {
            crate::simplicity::trace::provenance(message).unwrap_or_else(|| Part::Const(message.to_vec()))
        };
        self.log.push(Rec::Bytes(vec![Part::Const(head), body]));
    }
}

impl TranscriptBackend for CompileTranscript {
    fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        self.log_append(label, message);
        self.inner.append_message(label, message);
    }

    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        self.append_message(label, &x.to_le_bytes());
    }

    fn challenge_bytes(&mut self, label: &'static [u8], dest: &mut [u8]) {
        let mut request = vec![0x43];
        request.extend_from_slice(&le32(label.len()));
        request.extend_from_slice(label);
        request.extend_from_slice(&le32(dest.len()));
        let k = self.log.iter().filter(|r| matches!(r, Rec::Challenge { .. })).count();
        self.log.push(Rec::Challenge { request, len: dest.len() });
        self.inner.challenge_bytes(label, dest);
        crate::simplicity::trace::note_challenge(k, dest);
    }

    fn build_rng(&self) -> merlin::TranscriptRngBuilder {
        self.inner.build_rng()
    }
}

impl TranscriptRef for CompileTranscript {
    type Backend = Self;
    fn backend(&mut self) -> &mut Self {
        self
    }
    fn backend_ref(&self) -> &Self {
        self
    }
}

/// The constant bytes before the first part that is not constant (all of them if none).
pub(crate) fn prefix_len(log: &[Rec]) -> usize {
    let mut n = 0;
    for r in log {
        match r {
            Rec::Bytes(parts) => {
                for p in parts {
                    match p {
                        Part::Const(b) => n += b.len(),
                        _ => return n,
                    }
                }
            }
            Rec::Challenge { request, .. } => n += request.len(),
        }
    }
    n
}

/// The values of a challenge in the program.
pub(crate) struct ChallengeVals {
    /// The 32-byte output blocks `o_i` (the last one possibly longer than what the challenge uses).
    pub blocks: Vec<Val>,
    /// For a 64-byte challenge: the secp256k1 scalar `normalize(o0) · R + normalize(o1)`.
    pub scalar: Option<Val>,
}

/// The program's hashing state.
enum State {
    /// Every byte so far is constant (`h` hashes them).
    Const(Sha256, usize),
    /// A context in the program, and constant bytes not yet added to it.
    Prog(Val, Vec<u8>),
}

/// Lower a log into the program: the constant prefix up to its last 64-byte boundary (or up to
/// `force_from`, whichever is first) becomes a constant context, the rest is added with
/// `sha_256_ctx_8_add_*`. `parts` gives the values of a non-constant part (each with its byte
/// length, 1 or 32), given the challenges lowered so far. Challenges inside the constant prefix are computed here, as constants.
pub(crate) fn lower_log(p: &mut Prog, log: &[Rec], force_from: usize, parts: &mut dyn FnMut(&mut Prog, &Part, &[ChallengeVals]) -> Vec<(Val, usize)>) -> Vec<ChallengeVals> {
    let mut state = State::Const(Sha256::new(), 0);
    let mut prefix: Vec<u8> = Vec::new();
    let mut out = Vec::new();
    let to_prog = |p: &mut Prog, prefix: &[u8]| -> State {
        let full = prefix.len() / 64 * 64;
        let ctx = const_ctx(p, &prefix[..full]);
        State::Prog(ctx, prefix[full..].to_vec())
    };
    for r in log {
        match r {
            Rec::Bytes(ps) => {
                for part in ps {
                    match part {
                        Part::Const(b) => match &mut state {
                            State::Const(h, n) => {
                                // switch to the program at `force_from`
                                let mut b = &b[..];
                                if *n + b.len() > force_from {
                                    let k = force_from.saturating_sub(*n);
                                    h.update(&b[..k]);
                                    prefix.extend_from_slice(&b[..k]);
                                    *n += k;
                                    b = &b[k..];
                                    state = to_prog(p, &prefix);
                                    if let State::Prog(_, pend) = &mut state {
                                        pend.extend_from_slice(b);
                                    }
                                } else {
                                    h.update(b);
                                    prefix.extend_from_slice(b);
                                    *n += b.len();
                                }
                            }
                            State::Prog(_, pend) => pend.extend_from_slice(b),
                        },
                        other => {
                            if let State::Const(..) = state {
                                state = to_prog(p, &prefix);
                            }
                            let vals = parts(p, other, &out);
                            debug_assert_eq!(vals.iter().map(|v| v.1).sum::<usize>(), other.len());
                            if let State::Prog(ctx, pend) = &mut state {
                                let mut c = flush(p, *ctx, pend);
                                for (v, n) in vals {
                                    c = add(p, c, v, n);
                                }
                                *ctx = c;
                            }
                        }
                    }
                }
            }
            Rec::Challenge { request, len } => {
                let blocks = (len + 31) / 32;
                match &mut state {
                    State::Const(h, n) if *n + request.len() <= force_from => {
                        h.update(request);
                        prefix.extend_from_slice(request);
                        *n += request.len();
                        let mut bs = Vec::new();
                        let mut raw = Vec::new();
                        for i in 0..blocks {
                            let mut c = h.clone();
                            c.update((i as u64).to_le_bytes());
                            let o = c.finalize().to_vec();
                            raw.extend_from_slice(&o);
                            bs.push(p.push(Op::Const(Ty::word(), o)));
                        }
                        let scalar = (*len == 64).then(|| {
                            let mut w = [0u8; 64];
                            w.copy_from_slice(&raw[..64]);
                            let s = <k256::Scalar as crate::curve::Field>::from_wide(&w);
                            p.push(Op::Const(Ty::word(), crate::curve::Field::to_bytes32(&s).to_vec()))
                        });
                        out.push(ChallengeVals { blocks: bs, scalar });
                        continue;
                    }
                    State::Const(..) => {
                        state = to_prog(p, &prefix);
                    }
                    State::Prog(..) => {}
                }
                if let State::Prog(ctx, pend) = &mut state {
                    pend.extend_from_slice(request);
                    let c = flush(p, *ctx, pend);
                    *ctx = c;
                    let bs: Vec<Val> = (0..blocks)
                        .map(|i| {
                            let k = p.push(Op::Const(Ty::Word(64), (i as u64).to_le_bytes().to_vec()));
                            let ci = p.push(Op::Jet("sha_256_ctx_8_add_8", vec![c, k], Ty::Ctx));
                            p.push(Op::Jet("sha_256_ctx_8_finalize", vec![ci], Ty::word()))
                        })
                        .collect();
                    let scalar = (*len == 64).then(|| {
                        let a = p.push(Op::Jet("scalar_normalize", vec![bs[0]], Ty::word()));
                        let b = p.push(Op::Jet("scalar_normalize", vec![bs[1]], Ty::word()));
                        let r = p.push(Op::Const(Ty::word(), R_SECP256K1.to_vec()));
                        let ar = p.push(Op::Jet("scalar_multiply", vec![a, r], Ty::word()));
                        p.push(Op::Jet("scalar_add", vec![ar, b], Ty::word()))
                    });
                    out.push(ChallengeVals { blocks: bs, scalar });
                }
            }
        }
    }
    out
}

/// A context after the whole blocks `prefix` (a multiple of 64 bytes): the init jet's empty
/// buffer, the block count and the midstate.
fn const_ctx(p: &mut Prog, prefix: &[u8]) -> Val {
    let init = p.push(Op::Jet("sha_256_ctx_8_init", vec![], Ty::Ctx));
    if prefix.is_empty() {
        return init;
    }
    assert_eq!(prefix.len() % 64, 0);
    let mut state: [u32; 8] = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let blocks: Vec<sha2::digest::generic_array::GenericArray<u8, sha2::digest::consts::U64>> =
        prefix.chunks(64).map(|c| sha2::digest::generic_array::GenericArray::clone_from_slice(c)).collect();
    sha2::compress256(&mut state, &blocks);
    let mid: Vec<u8> = state.iter().flat_map(|w| w.to_be_bytes()).collect();
    let buf = p.push(Op::Fst(init, Ty::CtxBuf));
    let count = p.push(Op::Const(Ty::Word(64), ((prefix.len() / 64) as u64).to_be_bytes().to_vec()));
    let midv = p.push(Op::Const(Ty::word(), mid));
    let tail = p.push(Op::Pair(count, midv, Ty::prod(Ty::Word(64), Ty::word())));
    p.push(Op::Pair(buf, tail, Ty::Ctx))
}

/// Add constant bytes to a context in power-of-two chunks (64, 32, ..., 1).
fn flush(p: &mut Prog, mut ctx: Val, pend: &mut Vec<u8>) -> Val {
    let mut b = &pend[..];
    while !b.is_empty() {
        let n = [64usize, 32, 16, 8, 4, 2, 1].iter().copied().find(|n| *n <= b.len()).unwrap();
        let ty = if n == 64 { Ty::prod(Ty::word(), Ty::word()) } else { Ty::Word(8 * n as u32) };
        let k = p.push(Op::Const(ty, b[..n].to_vec()));
        ctx = add(p, ctx, k, n);
        b = &b[n..];
    }
    pend.clear();
    ctx
}

/// `sha_256_ctx_8_add_n(ctx, v)`.
fn add(p: &mut Prog, ctx: Val, v: Val, n: usize) -> Val {
    let jet = match n {
        1 => "sha_256_ctx_8_add_1",
        2 => "sha_256_ctx_8_add_2",
        4 => "sha_256_ctx_8_add_4",
        8 => "sha_256_ctx_8_add_8",
        16 => "sha_256_ctx_8_add_16",
        32 => "sha_256_ctx_8_add_32",
        64 => "sha_256_ctx_8_add_64",
        _ => unreachable!("chunks are powers of two up to 64"),
    };
    p.push(Op::Jet(jet, vec![ctx, v], Ty::Ctx))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::ir::{Op, Prog, Ty};
    use crate::simplicity::run::{dummy_env, execute_text_unbudgeted, sighash_of};
    use crate::{Sha256Transcript, TranscriptBackend};
    use std::collections::HashMap;

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    fn leak(b: Vec<u8>) -> &'static [u8] {
        Box::leak(b.into_boxed_slice())
    }

    #[test]
    fn compile_transcript_has_the_sha256_state() {
        let (mut a, mut b) = (CompileTranscript::new(b"t"), Sha256Transcript::new(b"t"));
        for t in [&mut a as &mut dyn TranscriptBackend, &mut b] {
            t.append_message(b"m", b"hello");
            t.append_u64(b"n", 7);
        }
        let (mut x, mut y) = ([0u8; 64], [0u8; 64]);
        a.challenge_bytes(b"c", &mut x);
        b.challenge_bytes(b"c", &mut y);
        assert_eq!(x, y);
        assert_eq!(a.log().len(), 5); // init block, dom-sep, m, n, challenge
    }

    /// Assert, in a program, that every full 32-byte block of every challenge equals `expected`
    /// (hex of the challenge bytes), and the scalar of 64-byte challenges equals `scalars`.
    fn check_log(log: &[Rec], force_from: usize, expected: &[Vec<u8>], scalars: &[Option<Vec<u8>>]) -> bool {
        let mut p = Prog::new();
        let mut parts = |p: &mut Prog, part: &Part, _: &[ChallengeVals]| match part {
            Part::Sighash => vec![(p.push(Op::Jet("sig_all_hash", vec![], Ty::word())), 32)],
            _ => unreachable!(),
        };
        let ch = lower_log(&mut p, log, force_from, &mut parts);
        assert_eq!(ch.len(), expected.len());
        for (i, c) in ch.iter().enumerate() {
            for (j, blk) in expected[i].chunks(32).enumerate() {
                if blk.len() == 32 {
                    let k = p.push(Op::Const(Ty::word(), blk.to_vec()));
                    let e = p.push(Op::Jet("eq_256", vec![c.blocks[j], k], Ty::Bit));
                    p.push(Op::Assert(e));
                }
            }
            if let Some(s) = &scalars[i] {
                let k = p.push(Op::Const(Ty::word(), s.clone()));
                let e = p.push(Op::Jet("eq_256", vec![c.scalar.unwrap(), k], Ty::Bit));
                p.push(Op::Assert(e));
            }
        }
        execute_text_unbudgeted(&p.to_text(), &HashMap::new(), &dummy_env()).is_ok()
    }

    /// The KATs of `tests/vectors/transcript/sha256.json`, hashed in the program (from the
    /// first block after the tag, and from the start), and a mutated expectation.
    #[test]
    fn program_challenges_match_the_kats() {
        let v: serde_json::Value = serde_json::from_str(include_str!("../../tests/vectors/transcript/sha256.json")).unwrap();
        let mut cases = 0;
        for case in v["cases"].as_array().unwrap() {
            let ops = case["ops"].as_array().unwrap();
            if ops.iter().any(|o| o[0] == "rng_digest") {
                continue;
            }
            let mut t = CompileTranscript::new(leak(unhex(case["label"].as_str().unwrap())));
            let outs = case["outputs"].as_array().unwrap();
            let (mut expected, mut scalars, mut k) = (Vec::new(), Vec::new(), 0);
            for o in ops {
                let label = || leak(unhex(o[1].as_str().unwrap()));
                match o[0].as_str().unwrap() {
                    "append" => t.append_message(label(), &unhex(o[2].as_str().unwrap())),
                    "u64" => t.append_u64(label(), o[2].as_u64().unwrap()),
                    "challenge" => {
                        let mut d = vec![0u8; o[2].as_u64().unwrap() as usize];
                        t.challenge_bytes(label(), &mut d);
                        assert_eq!(crate::simplicity::sha::tests::hexs(&d), outs[k].as_str().unwrap());
                        expected.push(d);
                        scalars.push(None);
                        k += 1;
                    }
                    "scalar_secp256k1" => {
                        let mut d = vec![0u8; 64];
                        t.challenge_bytes(label(), &mut d);
                        expected.push(d);
                        scalars.push(Some(unhex(outs[k].as_str().unwrap())));
                        k += 1;
                    }
                    "scalar_ristretto" => {
                        let mut d = vec![0u8; 64];
                        t.challenge_bytes(label(), &mut d);
                        expected.push(d);
                        scalars.push(None);
                        k += 1;
                    }
                    other => panic!("{}", other),
                }
            }
            for force in [64, 0] {
                assert!(check_log(t.log(), force, &expected, &scalars), "case {} force {}", case["name"], force);
            }
            let mut bad = expected.clone();
            bad[0][0] ^= 1;
            if bad[0].len() >= 32 {
                assert!(!check_log(t.log(), 64, &bad, &scalars), "case {}: a wrong expectation passed", case["name"]);
            }
            cases += 1;
        }
        assert!(cases >= 6);
    }

    fn hexs(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }

    /// The constant prefix ends at a block boundary, the rest is hashed in the program: every
    /// split of the prefix before the sighash gives the transcript's challenge.
    #[test]
    fn prefix_splits() {
        let env = dummy_env();
        let sighash = sighash_of(&env);
        // bytes before the sighash message: 64 (tag) + 17 (dom-sep "s") + (10 + filler) + 16 (sighash header)
        for target in [0usize, 1, 55, 56, 63] {
            let base = 64 + 17 + 10 + 16;
            let filler = (target + 64 * 4 - base % 64) % 64;
            let msg = vec![0xabu8; filler];
            let (mut c, mut s) = (CompileTranscript::new(b"s"), Sha256Transcript::new(b"s"));
            c.append_message(b"f", &msg);
            s.append_message(b"f", &msg);
            c.append_message(crate::simplicity::SIGHASH_LABEL, &[0u8; 32]);
            s.append_message(crate::simplicity::SIGHASH_LABEL, &sighash);
            let mut d = vec![0u8; 64];
            c.challenge_bytes(b"x", &mut [0u8; 64]);
            s.challenge_bytes(b"x", &mut d);
            let mut wide = [0u8; 64];
            wide.copy_from_slice(&d);
            let scalar = <k256::Scalar as crate::curve::Field>::from_wide(&wide);
            let sc = crate::curve::Field::to_bytes32(&scalar).to_vec();
            assert_eq!(prefix_len(c.log()) % 64, target, "the test's arithmetic");
            assert!(check_log(c.log(), usize::MAX, &[d.clone()], &[Some(sc.clone())]), "target {}", target);
            let mut bad = d.clone();
            bad[40] ^= 1;
            assert!(!check_log(c.log(), usize::MAX, &[bad], &[None]));
        }
    }
}

//! Compiling a lowered circuit into its Simplicity verifier: trace the BP++ verifier on a dummy
//! proof of the circuit's dimensions, lower the transcript log, the tape and the final
//! multiscalar multiplication into the IR, and keep what the witness of a real proof needs.

#![allow(non_snake_case)]

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use k256::elliptic_curve::ff::{Field as _, PrimeField as _};
use k256::elliptic_curve::sec1::ToEncodedPoint;

use crate::bppp::{BpppGens, BpppTranscript, CircuitProof, ReciprocalCircuit};
use crate::curve::{Curve, Field, PointEncoding, Secp256k1, Secp256k1Compressed};
use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::R1CSProof;
use crate::simplicity::ir::{Op, Prog, Ty, Val};
use crate::simplicity::point::{assert_infinity, const_gej, ge_to_gej, msm, witness_point, witness_scalar, WitPoint};
use crate::simplicity::run::{bit_value, execute_text, word_value, Env, ExecError, Report};
use crate::simplicity::sha::{lower_log, ChallengeVals, Part, Rec};
use crate::simplicity::trace::{register_witness_point, register_witness_scalar, with_tape, NodeId, PointSrc, TOp, Tape, Traced, TracedCurve, TracedPoint};
use crate::simplicity::CompileTranscript;

type K = k256::Scalar;

/// A Simplicity program that verifies the BP++ proofs of one circuit, bound to the spending
/// transaction (`jet_sig_all_hash` in the transcript).
#[derive(Clone, Debug)]
pub struct SimplicityVerifier {
    text: String,
    cmr: ::simplicity::Cmr,
    n_lin: usize,
    n_mm: usize,
    stats: Stats,
}

/// The witness of a proof: its points (as parity and x) and scalars, by witness name.
#[derive(Clone, Debug)]
pub struct SimplicityWitness(HashMap<Arc<str>, ::simplicity::Value>);

/// What the program contains.
#[derive(Clone, Debug)]
pub struct Stats {
    /// Jet calls by name.
    pub jets: BTreeMap<&'static str, usize>,
    /// Live operations of the traced verifier.
    pub tape_ops: usize,
    /// Terms of the final multiscalar multiplication.
    pub msm_terms: usize,
    /// Points of the proof (witness values).
    pub witness_points: usize,
    /// Scalars of the proof (witness values).
    pub witness_scalars: usize,
}

fn gadget_err(s: &str) -> R1CSError {
    R1CSError::GadgetError { description: s.into() }
}

impl SimplicityVerifier {
    /// The program's commitment Merkle root.
    pub fn cmr(&self) -> ::simplicity::Cmr {
        self.cmr
    }

    /// The program in Simplicity's human-readable encoding.
    pub fn to_text(&self) -> &str {
        &self.text
    }

    /// What the program contains.
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// The witness for `proof`: an error for a proof of other dimensions, with a point that is
    /// not on the curve or is the identity (the program cannot take it), or of the BP backend.
    pub fn witness(&self, proof: &R1CSProof<Secp256k1>) -> Result<SimplicityWitness, R1CSError> {
        let (cp, n_lin, n_mm) = proof.bppp_parts().ok_or_else(|| gadget_err("not a BP++ proof"))?;
        if (n_lin, n_mm) != (self.n_lin, self.n_mm) {
            return Err(gadget_err("a proof of other dimensions"));
        }
        let mut w = HashMap::new();
        for (i, c) in proof_points(cp).iter().enumerate() {
            let pt = Secp256k1::decompress(c).ok_or(R1CSError::VerificationError)?;
            let e = pt.to_affine().to_encoded_point(false);
            let (x, y) = match (e.x(), e.y()) {
                (Some(x), Some(y)) => (x.to_vec(), y.to_vec()),
                _ => return Err(gadget_err("the identity in a proof (not supported by the program)")),
            };
            w.insert(Arc::from(format!("p{}", i)), ::simplicity::Value::product(bit_value(y[31] & 1 == 1), word_value(&x)));
        }
        for (i, s) in cp.wnla.l.iter().chain(&cp.wnla.n).enumerate() {
            w.insert(Arc::from(format!("s{}", i)), word_value(&s.to_repr()));
        }
        Ok(SimplicityWitness(w))
    }

    /// Run the program with `w` in the transaction `env`, as a node would.
    pub fn execute(&self, w: &SimplicityWitness, env: &Env) -> Result<Report, ExecError> {
        execute_text(&self.text, &w.0, env)
    }
}

/// The proof's points in the order of its bytes: `C_L, C_R, C_O, C_S`, then `(X_r, R_r)` per round.
fn proof_points<C: Curve>(cp: &CircuitProof<C>) -> Vec<C::Compressed> {
    let mut v = vec![cp.C_L, cp.C_R, cp.C_O, cp.C_S];
    for (x, r) in cp.wnla.X.iter().zip(&cp.wnla.R) {
        v.push(*x);
        v.push(*r);
    }
    v
}

/// A dummy proof of the circuit's dimensions: random points (multiples of `G`) and scalars.
/// Random, so that no statement can be crafted to equal one of its points or scalars (the
/// tracer tells proof data from constants by their bytes); the program does not depend on it.
pub(crate) fn dummy_proof<R: rand_core::RngCore + rand_core::CryptoRng>(c: &ReciprocalCircuit<K>, rng: &mut R) -> (Vec<Secp256k1Compressed>, Vec<K>) {
    let (n_lin, n_mm) = (c.n_lin, c.n_p + c.n_m);
    let (k, af, bf) = crate::bppp::wnla::rounds(n_lin + crate::bppp::gens::H_FIXED, n_mm);
    let points = (0..4 + 2 * k).map(|_| Secp256k1::compress(&(k256::ProjectivePoint::GENERATOR * K::random(&mut *rng)))).collect();
    let scalars = (0..af + bf).map(|_| K::random(&mut *rng)).collect();
    (points, scalars)
}

/// The transcript domain of R1CS proofs on the BP++ backend (as `Verifier::verify_bppp`).
const BPPP_DOMAIN: &[u8] = b"bppp-r1cs v2";

/// Compile the lowered circuit `c` with statement `V`, whose verifier transcript so far is `t`.
pub(crate) fn compile(
    c: &ReciprocalCircuit<K>,
    V: &[Secp256k1Compressed],
    t: &CompileTranscript,
    pc: &PedersenGens<Secp256k1>,
    bp: &BulletproofGens<Secp256k1>,
) -> Result<SimplicityVerifier, R1CSError> {
    compile_with(c, V, t, pc, bp, &mut rand::rngs::OsRng)
}

/// [`compile`] with the randomness of the dummy proof.
pub(crate) fn compile_with<R: rand_core::RngCore + rand_core::CryptoRng>(
    c: &ReciprocalCircuit<K>,
    V: &[Secp256k1Compressed],
    t: &CompileTranscript,
    pc: &PedersenGens<Secp256k1>,
    bp: &BulletproofGens<Secp256k1>,
    rng: &mut R,
) -> Result<SimplicityVerifier, R1CSError> {
    if !t.log().iter().any(|r| matches!(r, Rec::Bytes(ps) if ps.contains(&Part::Sighash))) {
        return Err(gadget_err("the transcript has no sighash record (SIGHASH_LABEL)"));
    }
    let (n_lin, n_mm) = (c.n_lin, c.n_p + c.n_m);
    let gens = BpppGens::new(pc, bp, n_lin, n_mm).map_err(|_| R1CSError::InvalidGeneratorsLength)?;

    // a dummy proof of the circuit's dimensions; a constant point equal to one of its points
    // would be taken for proof data (negligible for random points unless crafted for them)
    let (points, scalars) = dummy_proof(c, rng);
    let (n_points, n_scalars) = (points.len(), scalars.len());
    let constants = V.iter().copied().chain(std::iter::once(gens.g).chain(gens.h.iter().copied()).chain(gens.n.iter().copied()).map(|p| Secp256k1::compress(&p)));
    for k in constants {
        if points.contains(&k) {
            return Err(gadget_err("a statement point equals a point of the dummy proof"));
        }
    }
    let mut bytes = Vec::new();
    for p in &points {
        bytes.extend_from_slice(p.as_bytes());
    }
    for s in &scalars {
        bytes.extend_from_slice(&s.to_repr());
    }

    // trace
    let ct = c.map_scalars(Traced::constant);
    let n: Vec<TracedPoint> = gens.n.iter().map(|p| TracedPoint::constant(*p)).collect();
    let tg = BpppGens::<TracedCurve> { g: TracedPoint::constant(gens.g), h: gens.h.iter().map(|p| TracedPoint::constant(*p)).collect(), n: &n };
    let mut tt = t.clone();
    let traced = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_tape(|| {
            for (i, p) in points.iter().enumerate() {
                register_witness_point(p, i);
            }
            for (i, s) in scalars.iter().enumerate() {
                register_witness_scalar(&<K as Field>::to_bytes32(s), i);
            }
            let tp = CircuitProof::<TracedCurve>::from_bytes_dims(&bytes, n_lin, n_mm)?;
            BpppTranscript::domain_sep(&mut tt, BPPP_DOMAIN);
            let terms = crate::bppp::reciprocal::terms(&tp, &ct, &tg, V, &mut tt)?;
            Ok::<_, crate::errors::ProofError>((terms, tt.log().to_vec()))
        })
    }));
    let ((terms, log), tape) = match traced {
        Ok((Ok(x), tape)) => (x, tape),
        Ok((Err(e), _)) => return Err(gadget_err(&format!("tracing the verifier failed: {:?}", e))),
        Err(e) => {
            let msg = e.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| e.downcast_ref::<String>().cloned()).unwrap_or_default();
            return Err(gadget_err(&format!("the verifier is not traceable: {}", msg)));
        }
    };

    // the program
    let mut p = Prog::new();
    let wp: Vec<WitPoint> = (0..n_points).map(|i| witness_point(&mut p, &format!("p{}", i))).collect();
    let ws: Vec<Val> = (0..n_scalars).map(|i| witness_scalar(&mut p, &format!("s{}", i))).collect();
    let roots: Vec<NodeId> = std::iter::once(&terms.g)
        .chain(&terms.h)
        .chain(&terms.n)
        .chain(terms.points.iter().map(|(k, _)| k))
        .filter_map(|t| t.node)
        .collect();
    let live = tape.live(&roots);
    let mut lw = TapeLowering { tape: &tape, live: &live, vals: HashMap::new(), ws: &ws };
    let challenges = {
        let mut parts = |p: &mut Prog, part: &Part, ch: &[ChallengeVals]| match part {
            Part::Sighash => vec![(p.push(Op::Jet("sig_all_hash", vec![], Ty::word())), 32)],
            Part::WitPoint(i) => vec![(wp[*i].sec1_prefix, 1), (wp[*i].x, 32)],
            Part::Scalar(n) => vec![(lw.node(p, NodeId(*n), ch), 32)],
            Part::Const(_) => unreachable!("constants are hashed by lower_log"),
        };
        lower_log(&mut p, &log, usize::MAX, &mut parts)
    };
    // every live node (the checks among them), in tape order
    for i in 0..tape.ops.len() {
        if live[i] {
            lw.node(&mut p, NodeId(i as u32), &challenges);
        }
    }
    let scalar = |p: &mut Prog, lw: &mut TapeLowering, t: &Traced| -> Option<Val> {
        match t.node {
            Some(n) => Some(lw.node(p, n, &challenges)),
            None if bool::from(t.value.is_zero()) => None,
            None => Some(p.push(Op::Const(Ty::word(), t.value.to_repr().to_vec()))),
        }
    };
    let mut msm_terms = Vec::new();
    let generators = std::iter::once((&terms.g, gens.g)).chain(terms.h.iter().zip(gens.h.iter().copied())).chain(terms.n.iter().zip(gens.n.iter().copied()));
    for (k, pt) in generators {
        if let Some(kv) = scalar(&mut p, &mut lw, k) {
            let g = const_gej(&mut p, &pt.to_affine());
            msm_terms.push((kv, g));
        }
    }
    for (k, pt) in &terms.points {
        // a constant identity (a commitment to zero with a zero blinding) adds nothing
        if pt.src == PointSrc::Const && bool::from(group::Group::is_identity(&pt.value)) {
            continue;
        }
        if let Some(kv) = scalar(&mut p, &mut lw, k) {
            let g = match pt.src {
                PointSrc::Witness(i) => ge_to_gej(&mut p, wp[i].ge),
                PointSrc::Const => const_gej(&mut p, &pt.value.to_affine()),
            };
            msm_terms.push((kv, g));
        }
    }
    let acc = msm(&mut p, &msm_terms);
    assert_infinity(&mut p, acc);

    let text = p.to_text();
    let forest = ::simplicity::human_encoding::Forest::parse::<::simplicity::jet::Elements>(&text)
        .map_err(|e| gadget_err(&format!("the generated program does not parse: {}", e)))?;
    let cmr = forest.roots().get("main").expect("main").cmr();
    let stats = Stats { jets: p.stats(), tape_ops: live.iter().filter(|x| **x).count(), msm_terms: msm_terms.len(), witness_points: n_points, witness_scalars: n_scalars };
    Ok(SimplicityVerifier { text, cmr, n_lin, n_mm, stats })
}

/// Tape nodes as IR values, lowered on demand (a node's arguments come before it).
struct TapeLowering<'a> {
    tape: &'a Tape,
    live: &'a [bool],
    vals: HashMap<NodeId, Val>,
    ws: &'a [Val],
}

impl<'a> TapeLowering<'a> {
    fn node(&mut self, p: &mut Prog, n: NodeId, ch: &[ChallengeVals]) -> Val {
        if let Some(v) = self.vals.get(&n) {
            return *v;
        }
        debug_assert!(self.live[n.0 as usize]);
        let op = self.tape.ops[n.0 as usize];
        for a in op.args() {
            self.node(p, a, ch);
        }
        let g = |s: &Self, a: NodeId| s.vals[&a];
        let w = Ty::word();
        let konst = |p: &mut Prog, c: &crate::simplicity::trace::ScalarBytes| p.push(Op::Const(Ty::word(), c.0.to_vec()));
        let v = match op {
            TOp::WitScalar(i) => self.ws[i],
            TOp::Challenge(k) => ch.get(k).and_then(|c| c.scalar).expect("a challenge lowered before its use"),
            TOp::Add(a, b) => p.push(Op::Jet("scalar_add", vec![g(self, a), g(self, b)], w)),
            TOp::Sub(a, b) => {
                let nb = p.push(Op::Jet("scalar_negate", vec![g(self, b)], w.clone()));
                p.push(Op::Jet("scalar_add", vec![g(self, a), nb], w))
            }
            TOp::Mul(a, b) => p.push(Op::Jet("scalar_multiply", vec![g(self, a), g(self, b)], w)),
            TOp::Neg(a) => p.push(Op::Jet("scalar_negate", vec![g(self, a)], w)),
            TOp::Invert(a) => p.push(Op::Jet("scalar_invert", vec![g(self, a)], w)),
            TOp::AddC(a, c) => {
                let k = konst(p, &c);
                p.push(Op::Jet("scalar_add", vec![g(self, a), k], w))
            }
            TOp::MulC(a, c) => {
                let k = konst(p, &c);
                p.push(Op::Jet("scalar_multiply", vec![g(self, a), k], w))
            }
            TOp::AssertNonzero(a) => {
                let z = p.push(Op::Jet("scalar_is_zero", vec![g(self, a)], Ty::Bit));
                let nz = p.push(Op::Jet("complement_1", vec![z], Ty::Bit));
                p.push(Op::Assert(nz));
                g(self, a)
            }
            TOp::AssertEq(a, c) => {
                let k = konst(p, &c);
                let e = p.push(Op::Jet("eq_256", vec![g(self, a), k], Ty::Bit));
                p.push(Op::Assert(e));
                g(self, a)
            }
            TOp::AssertNe(a, c) => {
                let k = konst(p, &c);
                let e = p.push(Op::Jet("eq_256", vec![g(self, a), k], Ty::Bit));
                let ne = p.push(Op::Jet("complement_1", vec![e], Ty::Bit));
                p.push(Op::Assert(ne));
                g(self, a)
            }
        };
        self.vals.insert(n, v);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::{lc, Backend, ConstraintSystem, Prover, Variable, Verifier};
    use crate::simplicity::run::{dummy_env, sighash_of};
    use crate::simplicity::SIGHASH_LABEL;
    use crate::{Sha256Transcript, TranscriptBackend};

    use rand_chacha::rand_core::SeedableRng;

    fn product<CS: ConstraintSystem<K>>(cs: &mut CS, x: Variable, y: Variable) {
        let (_, _, o) = cs.multiply(lc(x), lc(y));
        cs.constrain(lc(o) - K::from(15u64));
    }

    fn gens() -> (PedersenGens<Secp256k1>, BulletproofGens<Secp256k1>) {
        (PedersenGens::for_curve(), BulletproofGens::for_curve(64, 1))
    }

    /// The circuit and the compile transcript for statement `V`.
    fn lowered(V: &[Secp256k1Compressed]) -> (ReciprocalCircuit<K>, CompileTranscript) {
        let mut ct = CompileTranscript::new(b"test");
        TranscriptBackend::append_message(&mut ct, SIGHASH_LABEL, &[0u8; 32]);
        let c = {
            let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
            v.set_backend(Backend::Bppp);
            let (x, y) = (v.commit(V[0]), v.commit(V[1]));
            product(&mut v, x, y);
            v.lower_builder_bppp().unwrap()
        };
        (c, ct)
    }

    /// A statement point equal to a point of the dummy proof would be taken for a witness
    /// point (provenance is by bytes): the compiler refuses it.
    #[test]
    fn statement_point_equal_to_a_dummy_point_is_refused() {
        let (pc, bp) = gens();
        let seed = 9;
        let (c0, _) = lowered(&[Secp256k1::compress(&k256::ProjectivePoint::GENERATOR), Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)]);
        let (points, _) = dummy_proof(&c0, &mut rand_chacha::ChaCha20Rng::seed_from_u64(seed));
        let V = [points[0], Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)];
        let (c, ct) = lowered(&V);
        let r = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(seed));
        assert!(r.is_err(), "a statement point equal to a dummy point compiled");
    }

    /// The dummy proof is random, the program is not.
    #[test]
    fn program_does_not_depend_on_the_dummy_proof() {
        let (pc, bp) = gens();
        let g = Secp256k1::compress(&(k256::ProjectivePoint::GENERATOR * K::from(5u64)));
        let V = [g, Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)];
        let (c, ct) = lowered(&V);
        let a = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(1)).unwrap();
        let b = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(2)).unwrap();
        assert_eq!(a.to_text(), b.to_text());
    }

    /// The program's own checks, not the witness builder's: a point not on the curve and a
    /// scalar not below the group order make it fail.
    #[test]
    fn program_rejects_bad_witness_values() {
        let env = dummy_env();
        let (pc, bp) = gens();
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let mut t = Sha256Transcript::new(b"test");
        t.append_message(SIGHASH_LABEL, &sighash_of(&env));
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(Backend::Bppp);
        let (cx, x) = p.commit(K::from(3u64), K::random(&mut rng));
        let (cy, y) = p.commit(K::from(5u64), K::random(&mut rng));
        product(&mut p, x, y);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
        let V = [cx, cy];
        let (c, ct) = lowered(&V);
        let sv = compile(&c, &V, &ct, &pc, &bp).unwrap();
        let w = sv.witness(&proof).unwrap();
        assert!(sv.execute(&w, &env).is_ok());
        // x = 0 is on no point of secp256k1
        let mut bad = w.clone();
        bad.0.insert(Arc::from("p0"), ::simplicity::Value::product(bit_value(false), word_value(&[0u8; 32])));
        assert!(sv.execute(&bad, &env).is_err());
        // the group order itself
        let n = [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf,
            0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41,
        ];
        let mut bad = w.clone();
        bad.0.insert(Arc::from("s0"), word_value(&n));
        assert!(sv.execute(&bad, &env).is_err());
    }
}

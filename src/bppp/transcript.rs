//! Fiat–Shamir interface of the BP++ protocols.

use merlin::Transcript;

use crate::curve::{Curve, Field, PointEncoding};

/// What the BP++ protocols need from a transcript. `merlin::Transcript` in production; the
/// test-vector tests use a replaying transcript (fixed challenges, recorded messages).
pub trait BpppTranscript {
    /// Absorb a domain separator.
    fn domain_sep(&mut self, label: &'static [u8]);
    /// Absorb the curve's name, for every curve but ristretto255 (whose transcripts stay as
    /// they were before curves were generic).
    fn curve_domain_sep<C: Curve>(&mut self) {
        if C::NAME != "ristretto255" {
            self.append_message(b"curve", C::NAME.as_bytes());
        }
    }
    /// Absorb a point (its encoding).
    fn append_point<P: PointEncoding>(&mut self, label: &'static [u8], p: &P) {
        self.append_message(label, p.as_bytes());
    }
    /// Absorb a length or another public integer.
    fn append_u64(&mut self, label: &'static [u8], x: u64);
    /// Absorb a public scalar (its 32-byte encoding).
    fn append_scalar<S: Field>(&mut self, label: &'static [u8], s: &S) {
        self.append_message(label, &s.to_bytes32());
    }
    /// Absorb public bytes (a digest).
    fn append_message(&mut self, label: &'static [u8], m: &[u8]);
    /// Squeeze a challenge.
    fn challenge<S: Field>(&mut self, label: &'static [u8]) -> S;
    /// The start of the prover's RNG, bound to everything absorbed so far (spec §1). The
    /// default binds nothing; `merlin::Transcript` binds its state, as BP does.
    fn rng_builder(&self) -> merlin::TranscriptRngBuilder {
        Transcript::new(b"bppp-prover-rng v1").build_rng()
    }
}

impl BpppTranscript for Transcript {
    fn domain_sep(&mut self, label: &'static [u8]) {
        Transcript::append_message(self, b"dom-sep", label);
    }

    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        Transcript::append_u64(self, label, x);
    }

    fn append_message(&mut self, label: &'static [u8], m: &[u8]) {
        Transcript::append_message(self, label, m);
    }

    fn challenge<S: Field>(&mut self, label: &'static [u8]) -> S {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        S::from_wide(&buf)
    }

    fn rng_builder(&self) -> merlin::TranscriptRngBuilder {
        self.build_rng()
    }
}

/// The prover's randomness (spec §1): the transcript's RNG (bound to the statement and
/// everything the caller absorbed), rekeyed with the protocol, the circuit digest and a hash of
/// the witness, finalized with the caller's RNG. Defense in depth against a weak RNG.
pub(crate) fn prover_rng<'a, T, R, I, S>(transcript: &T, label: &'static [u8], digest: &[u8; 32], secrets: I, rng: &mut R) -> merlin::TranscriptRng
where
    T: BpppTranscript + ?Sized,
    R: rand_core::RngCore + rand_core::CryptoRng,
    I: Iterator<Item = &'a S>,
    S: Field,
{
    use clear_on_drop::clear::Clear;
    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    for s in secrets {
        let mut b = s.to_bytes32();
        h.update(b);
        b.clear();
    }
    let mut wh: [u8; 32] = h.finalize().into();
    let b = transcript
        .rng_builder()
        .rekey_with_witness_bytes(b"protocol", label)
        .rekey_with_witness_bytes(b"digest", digest)
        .rekey_with_witness_bytes(b"witness", &wh);
    wh.clear();
    b.finalize(rng)
}

/// Test transcript: hands out the given challenges in order and records every absorbed
/// message as `(label, bytes)`, so tests check the values (against the reference), the
/// order and what each challenge binds. The challenges are kept as their 32-byte encodings
/// and handed out in the field the protocol asks for.
#[cfg(test)]
pub(crate) struct Replay {
    pub challenges: alloc::collections::VecDeque<[u8; 32]>,
    pub log: alloc::vec::Vec<(&'static [u8], alloc::vec::Vec<u8>)>,
}

#[cfg(test)]
impl Replay {
    pub fn new<S: Field>(challenges: alloc::vec::Vec<S>) -> Self {
        Replay { challenges: challenges.iter().map(|c| c.to_bytes32()).collect(), log: alloc::vec::Vec::new() }
    }
}

#[cfg(test)]
impl BpppTranscript for Replay {
    fn domain_sep(&mut self, label: &'static [u8]) {
        self.log.push((label, alloc::vec::Vec::new()));
    }
    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        self.log.push((label, x.to_le_bytes().to_vec()));
    }
    fn append_message(&mut self, label: &'static [u8], m: &[u8]) {
        self.log.push((label, m.to_vec()));
    }
    fn challenge<S: Field>(&mut self, label: &'static [u8]) -> S {
        self.log.push((label, alloc::vec::Vec::new()));
        let c = self.challenges.pop_front().expect("more challenges than in the vector");
        S::from_bytes32(&c).expect("a canonical challenge")
    }
}

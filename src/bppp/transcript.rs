//! Fiat–Shamir interface of the BP++ protocols.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// What the BP++ protocols need from a transcript. `merlin::Transcript` in production; the
/// test-vector tests use a replaying transcript (fixed challenges, recorded messages).
pub trait BpppTranscript {
    /// Absorb a domain separator.
    fn domain_sep(&mut self, label: &'static [u8]);
    /// Absorb a point.
    fn append_point(&mut self, label: &'static [u8], p: &CompressedRistretto);
    /// Absorb a length or another public integer.
    fn append_u64(&mut self, label: &'static [u8], x: u64);
    /// Absorb a public scalar.
    fn append_scalar(&mut self, label: &'static [u8], s: &Scalar);
    /// Absorb public bytes (a digest).
    fn append_message(&mut self, label: &'static [u8], m: &[u8]);
    /// Squeeze a challenge.
    fn challenge(&mut self, label: &'static [u8]) -> Scalar;
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

    fn append_point(&mut self, label: &'static [u8], p: &CompressedRistretto) {
        Transcript::append_message(self, label, p.as_bytes());
    }

    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        Transcript::append_u64(self, label, x);
    }

    fn append_scalar(&mut self, label: &'static [u8], s: &Scalar) {
        Transcript::append_message(self, label, s.as_bytes());
    }

    fn append_message(&mut self, label: &'static [u8], m: &[u8]) {
        Transcript::append_message(self, label, m);
    }

    fn challenge(&mut self, label: &'static [u8]) -> Scalar {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }

    fn rng_builder(&self) -> merlin::TranscriptRngBuilder {
        self.build_rng()
    }
}

/// The prover's randomness (spec §1): the transcript's RNG (bound to the statement and
/// everything the caller absorbed), rekeyed with the protocol, the circuit digest and a hash of
/// the witness, finalized with the caller's RNG. Defense in depth against a weak RNG.
pub(crate) fn prover_rng<'a, T, R, I>(transcript: &T, label: &'static [u8], digest: &[u8; 32], secrets: I, rng: &mut R) -> merlin::TranscriptRng
where
    T: BpppTranscript + ?Sized,
    R: rand_core::RngCore + rand_core::CryptoRng,
    I: Iterator<Item = &'a Scalar>,
{
    use clear_on_drop::clear::Clear;
    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    for s in secrets {
        h.update(s.as_bytes());
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
/// order and what each challenge binds.
#[cfg(test)]
pub(crate) struct Replay {
    pub challenges: alloc::collections::VecDeque<Scalar>,
    pub log: alloc::vec::Vec<(&'static [u8], alloc::vec::Vec<u8>)>,
}

#[cfg(test)]
impl Replay {
    pub fn new(challenges: alloc::vec::Vec<Scalar>) -> Self {
        Replay { challenges: challenges.into(), log: alloc::vec::Vec::new() }
    }
}

#[cfg(test)]
impl BpppTranscript for Replay {
    fn domain_sep(&mut self, label: &'static [u8]) {
        self.log.push((label, alloc::vec::Vec::new()));
    }
    fn append_point(&mut self, label: &'static [u8], p: &CompressedRistretto) {
        self.log.push((label, p.as_bytes().to_vec()));
    }
    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        self.log.push((label, x.to_le_bytes().to_vec()));
    }
    fn append_scalar(&mut self, label: &'static [u8], s: &Scalar) {
        self.log.push((label, s.as_bytes().to_vec()));
    }
    fn append_message(&mut self, label: &'static [u8], m: &[u8]) {
        self.log.push((label, m.to_vec()));
    }
    fn challenge(&mut self, label: &'static [u8]) -> Scalar {
        self.log.push((label, alloc::vec::Vec::new()));
        self.challenges.pop_front().expect("more challenges than in the vector")
    }
}

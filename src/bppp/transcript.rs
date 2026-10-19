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

//! Batch verification (paper §4.3, last paragraph; spec §3.11): the verification equations of
//! several proofs over the same `PedersenGens` and `BulletproofGens`, combined with random
//! weights into one multiscalar multiplication. A batch that fails says only that some proof
//! is invalid; verify the proofs one by one to find which.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};

use super::circuit::{ArithmeticCircuit, CircuitProof, Terms};
use super::gens::BpppGens;
use super::mact::{MactProof, MactStatement};
use super::range::{RangeProof, RangeStatement};
use super::reciprocal::{self, ReciprocalCircuit};
use super::transcript::BpppTranscript;
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// Accumulates proofs; [`BatchVerifier::verify`] checks them all at once. Each `add_*` replays
/// the proof's transcript (so a malformed proof or a failed check of the statement is an error
/// right away) and adds its equation with a fresh random weight from `rng`.
pub struct BatchVerifier<'a, R: RngCore + CryptoRng> {
    pc: &'a PedersenGens,
    bp: &'a BulletproofGens,
    rng: R,
    acc: Terms,
}

impl<'a, R: RngCore + CryptoRng> BatchVerifier<'a, R> {
    /// An empty batch for proofs over these generators; `rng` draws the weights and must be
    /// unpredictable to the provers (a cryptographic RNG of the verifier, never a transcript).
    pub fn new(pc: &'a PedersenGens, bp: &'a BulletproofGens, rng: R) -> Self {
        BatchVerifier { pc, bp, rng, acc: Terms::default() }
    }

    fn add(&mut self, t: Terms) {
        let w = Scalar::random(&mut self.rng);
        self.acc.add_scaled(w, t);
    }

    /// Add an arithmetic circuit proof ([`CircuitProof::verify`]); `gens` must come from this
    /// batch's `PedersenGens` and `BulletproofGens`.
    pub fn add_circuit<T: BpppTranscript>(
        &mut self,
        proof: &CircuitProof,
        c: &ArithmeticCircuit,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let gens = c.gens(self.pc, self.bp)?;
        let t = proof.terms(c, &gens, V, transcript)?;
        self.add(t);
        Ok(())
    }

    /// Add a reciprocal form proof ([`reciprocal::verify`]).
    pub fn add_reciprocal<T: BpppTranscript>(
        &mut self,
        proof: &CircuitProof,
        c: &ReciprocalCircuit,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let gens = c.gens(self.pc, self.bp)?;
        let t = reciprocal::terms(proof, c, &gens, V, transcript)?;
        self.add(t);
        Ok(())
    }

    /// Add a range proof ([`RangeProof::verify`]).
    pub fn add_range<T: BpppTranscript>(
        &mut self,
        proof: &RangeProof,
        st: &RangeStatement,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let t = proof.terms(st, self.pc, self.bp, V, transcript)?;
        self.add(t);
        Ok(())
    }

    /// Add a multi-asset transaction proof ([`MactProof::verify`]).
    pub fn add_mact<T: BpppTranscript>(
        &mut self,
        proof: &MactProof,
        st: &MactStatement,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let t = proof.terms(st, self.pc, self.bp, V, transcript)?;
        self.add(t);
        Ok(())
    }

    /// Check all the proofs added (an empty batch verifies).
    pub fn verify(self) -> Result<(), ProofError> {
        if self.acc.is_empty() {
            return Ok(());
        }
        // Every proof added had generators of at most these sizes from the same setup.
        let gens = BpppGens::new(self.pc, self.bp, self.acc.h.len().saturating_sub(super::gens::H_FIXED), self.acc.n.len())?;
        self.acc.check(&gens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// Circuit and reciprocal proofs in one batch, also next to a range proof; a bad one fails.
    #[test]
    fn circuits_and_reciprocals() {
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(256, 1);
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let st = RangeStatement::new(16, alloc::vec![(0, 1 << 64)]).unwrap();
        let (rc, info) = st.circuit();
        let g = st.gens(&pc, &bp).unwrap();
        let s = Scalar::from(3u64);
        let w = info.witness(&[12345], &[s], &[crate::bppp::range::decompose(12345, &info.layouts[0])]);
        let V = alloc::vec![pc.commit(Scalar::from(12345u64), s).compress()];
        let rp = reciprocal::prove(&rc, &g, &V, &w, &mut Transcript::new(b"r"), &mut rng).unwrap();
        // the compiled circuit for some alpha is an arithmetic circuit with a witness
        let alpha = Scalar::from(99u64);
        let (ac, aw) = rc.compiled_for_test(&w, Scalar::ZERO, alpha);
        let ag = BpppGens::new(&pc, &bp, ac.n_lin, ac.n_m).unwrap();
        let cp = super::super::circuit::prove(&ac, &ag, &V, &aw, &mut Transcript::new(b"c"), &mut rng).unwrap();
        let run = |rp: &CircuitProof, cp: &CircuitProof| {
            let mut b = BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(2));
            b.add_reciprocal(rp, &rc, &V, &mut Transcript::new(b"r"))?;
            b.add_circuit(cp, &ac, &V, &mut Transcript::new(b"c"))?;
            b.verify()
        };
        run(&rp, &cp).unwrap();
        let mut bad = cp.clone();
        bad.wnla.n[0] += Scalar::ONE;
        assert!(run(&rp, &bad).is_err());
        let mut bad = rp.clone();
        bad.wnla.l[0] += Scalar::ONE;
        assert!(run(&bad, &cp).is_err());
    }
}

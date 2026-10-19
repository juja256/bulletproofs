//! Generators of the circuit protocol (spec §3.2).

use alloc::vec::Vec;
use core::iter::once;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// The generators of one circuit shape, taken from the BP generators so that both backends
/// share one setup: `G = B`, `H = [B_blinding, H_0, ..., H_{5 + n_lin}]`, `N = G_0..G_{n_m}`
/// (party 0 of `BulletproofGens`).
pub struct BpppGens<'a> {
    /// Value generator `G`.
    pub g: RistrettoPoint,
    /// Blinding and linear-part generators, `7 + n_lin` of them; `h[0]` blinds the inputs.
    pub h: Vec<RistrettoPoint>,
    /// Norm-part generators, `n_m` of them.
    pub n: &'a [RistrettoPoint],
}

impl<'a> BpppGens<'a> {
    /// Generators for a linear part of length `n_lin` and `n_m` multiplications; needs a
    /// `BulletproofGens` capacity of at least `max(n_m, n_lin + 6)`.
    pub fn new(pc: &PedersenGens, bp: &'a BulletproofGens, n_lin: usize, n_m: usize) -> Result<Self, ProofError> {
        let need = n_m.max(n_lin.checked_add(6).ok_or(ProofError::InvalidGeneratorsLength)?);
        if bp.party_capacity < 1 || bp.gens_capacity < need {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let (G, H) = bp.share(0).G_H_slices(need);
        let h = once(pc.B_blinding).chain(H[..6 + n_lin].iter().copied()).collect();
        Ok(BpppGens { g: pc.B, h, n: &G[..n_m] })
    }

    /// Commitment to an input vector `v` with blinding `s`:
    /// `v_0 G + s H_0 + sum_{j >= 1} v_j H_{6 + j}` (constant time). For a single value this
    /// is `PedersenGens::commit(v_0, s)`. Panics if `v` is empty or longer than `n_lin + 1`.
    pub fn commit_input(&self, v: &[Scalar], s: Scalar) -> RistrettoPoint {
        assert!(!v.is_empty() && v.len() + 6 <= self.h.len(), "input length does not fit the generators");
        RistrettoPoint::multiscalar_mul(
            once(v[0]).chain(once(s)).chain(v[1..].iter().copied()),
            once(&self.g).chain(once(&self.h[0])).chain(self.h[7..6 + v.len()].iter()),
        )
    }
}

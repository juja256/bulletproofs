//! Generators of the circuit protocol (spec §3.2).

use alloc::vec::Vec;
use core::iter::once;


use crate::curve::{Curve, Ristretto};
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// Generators of `H` before the linear part: `H_0` (the blinding generator, also of the
/// inputs) and `H_1..H_6`; together they carry the blinding vector `r_X[1..8]` of every
/// commitment (spec §3.2–3.3). The linear part starts at `H_7`.
pub(crate) const H_FIXED: usize = 7;

/// The generators of one circuit shape, taken from the BP generators so that both backends
/// share one setup: `G = B`, `H = [B_blinding, H_0, ..., H_{5 + n_lin}]`, `N = G_0..G_{n_m}`
/// (party 0 of `BulletproofGens`).
pub struct BpppGens<'a, C: Curve = Ristretto> {
    /// Value generator `G`.
    pub g: C::Point,
    /// Blinding and linear-part generators, `H_FIXED + n_lin` (`7 + n_lin`) of them; `h[0]`
    /// blinds the inputs.
    pub h: Vec<C::Point>,
    /// Norm-part generators, `n_m` of them.
    pub n: &'a [C::Point],
}

impl<'a, C: Curve> BpppGens<'a, C> {
    /// Generators for a linear part of length `n_lin` and `n_m` norm slots; needs a
    /// `BulletproofGens` capacity of at least [`BpppGens::capacity`]`(n_lin, n_m)`.
    pub fn new(pc: &PedersenGens<C>, bp: &'a BulletproofGens<C>, n_lin: usize, n_m: usize) -> Result<Self, ProofError> {
        let from_bp = n_lin.checked_add(H_FIXED - 1).ok_or(ProofError::InvalidGeneratorsLength)?;
        let need = n_m.max(from_bp);
        if bp.party_capacity < 1 || bp.gens_capacity < need {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let (G, H) = bp.share(0).G_H_slices(need);
        let h = once(pc.B_blinding).chain(H[..from_bp].iter().copied()).collect();
        Ok(BpppGens { g: pc.B, h, n: &G[..n_m] })
    }

    /// The `BulletproofGens` capacity for a linear part of length `n_lin` and `n_m` norm
    /// slots: `max(n_m, n_lin + 6)` (`H_0` is `B_blinding`, not taken from `BulletproofGens`).
    pub fn capacity(n_lin: usize, n_m: usize) -> usize {
        capacity(n_lin, n_m)
    }

    /// `InvalidGeneratorsLength` unless these are the generators for `n_lin` and `n_m`.
    pub(crate) fn check_dims(&self, n_lin: usize, n_m: usize) -> Result<(), ProofError> {
        if n_lin.checked_add(H_FIXED) != Some(self.h.len()) || self.n.len() != n_m {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        Ok(())
    }

    /// Commitment to an input vector `v` with blinding `s`:
    /// `v_0 G + s H_0 + sum_{j >= 1} v_j H_{6 + j}` (constant time). For a single value this
    /// is `PedersenGens::commit(v_0, s)`. Panics if `v` is empty or longer than `n_lin + 1`.
    pub fn commit_input(&self, v: &[C::Scalar], s: C::Scalar) -> C::Point {
        assert!(!v.is_empty() && v.len() + H_FIXED - 1 <= self.h.len(), "input length does not fit the generators");
        let scalars: Vec<C::Scalar> = once(v[0]).chain(once(s)).chain(v[1..].iter().copied()).collect();
        let points: Vec<C::Point> =
            once(self.g).chain(once(self.h[0])).chain(self.h[H_FIXED..H_FIXED - 1 + v.len()].iter().copied()).collect();
        C::msm_ct(&scalars, &points)
    }
}

/// [`BpppGens::capacity`], which does not depend on the curve.
pub(crate) fn capacity(n_lin: usize, n_m: usize) -> usize {
    n_m.max(n_lin.saturating_add(H_FIXED - 1))
}

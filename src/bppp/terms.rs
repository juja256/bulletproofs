//! A verification equation as a linear combination over the generators, checked by one
//! multiscalar multiplication (spec §2.4, §3.7) or accumulated for batch verification (§3.11).

use alloc::vec::Vec;
use core::iter::once;

use ff::Field as _;
use group::Group;

use super::gens::BpppGens;
use crate::curve::{Curve, Ristretto};
use crate::errors::ProofError;

/// `g G + <h, H> + <n, N> + sum k P = 0` over the generators `G`, `H`, `N` and the proof's own
/// points `P` (shorter `h`, `n` are zero-padded).
pub(crate) struct Terms<C: Curve = Ristretto> {
    pub(crate) g: C::Scalar,
    pub(crate) h: Vec<C::Scalar>,
    pub(crate) n: Vec<C::Scalar>,
    pub(crate) points: Vec<(C::Scalar, C::Point)>,
}

impl<C: Curve> Default for Terms<C> {
    fn default() -> Self {
        Terms { g: C::Scalar::ZERO, h: Vec::new(), n: Vec::new(), points: Vec::new() }
    }
}

impl<C: Curve> Terms<C> {
    /// Over the generators of [`BpppGens`].
    pub(crate) fn check(&self, gens: &BpppGens<C>) -> Result<(), ProofError> {
        self.check_with(&gens.g, &gens.h, gens.n)
    }

    /// Over the generators `g`, `h`, `n` (at least as long as the coefficients); public
    /// scalars, variable time.
    pub(crate) fn check_with(&self, g: &C::Point, h: &[C::Point], n: &[C::Point]) -> Result<(), ProofError> {
        let ks: Vec<C::Scalar> = once(self.g).chain(self.points.iter().map(|(k, _)| *k)).collect();
        let ps: Vec<C::Point> = once(*g).chain(self.points.iter().map(|(_, p)| *p)).collect();
        let check = C::msm_vt(&ks, &ps) + C::msm_vt(&self.h, &h[..self.h.len()]) + C::msm_vt(&self.n, &n[..self.n.len()]);
        if bool::from(check.is_identity()) {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// `self += w t` (batch verification).
    pub(crate) fn add_scaled(&mut self, w: C::Scalar, t: Terms<C>) {
        self.g += w * t.g;
        for (v, x) in [(&mut self.h, &t.h), (&mut self.n, &t.n)] {
            if v.len() < x.len() {
                v.resize(x.len(), C::Scalar::ZERO);
            }
            for (a, b) in v.iter_mut().zip(x) {
                *a += w * b;
            }
        }
        self.points.extend(t.points.into_iter().map(|(k, p)| (w * k, p)));
    }

    /// No terms at all (an empty batch).
    pub(crate) fn is_empty(&self) -> bool {
        self.points.is_empty() && self.h.is_empty() && self.n.is_empty()
    }
}

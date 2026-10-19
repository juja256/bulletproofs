//! A verification equation as a linear combination over the generators, checked by one
//! multiscalar multiplication (spec §2.4, §3.7) or accumulated for batch verification (§3.11).

use alloc::vec::Vec;
use core::iter::once;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use super::gens::BpppGens;
use crate::errors::ProofError;
use crate::util;

/// `g G + <h, H> + <n, N> + sum k P = 0` over the generators `G`, `H`, `N` and the proof's own
/// points `P` (shorter `h`, `n` are zero-padded).
#[derive(Default)]
pub(crate) struct Terms {
    pub(crate) g: Scalar,
    pub(crate) h: Vec<Scalar>,
    pub(crate) n: Vec<Scalar>,
    pub(crate) points: Vec<(Scalar, RistrettoPoint)>,
}

impl Terms {
    /// Over the generators of [`BpppGens`].
    pub(crate) fn check(&self, gens: &BpppGens) -> Result<(), ProofError> {
        self.check_with(&gens.g, &gens.h, gens.n)
    }

    /// Over the generators `g`, `h`, `n` (at least as long as the coefficients); public
    /// scalars, variable time.
    pub(crate) fn check_with(&self, g: &RistrettoPoint, h: &[RistrettoPoint], n: &[RistrettoPoint]) -> Result<(), ProofError> {
        let small = RistrettoPoint::vartime_multiscalar_mul(
            once(self.g).chain(self.points.iter().map(|(k, _)| *k)),
            once(g).chain(self.points.iter().map(|(_, p)| p)),
        );
        let check = small
            + util::vartime_msm_slices(&self.h, &h[..self.h.len()], util::MSM_CHUNK_VT)
            + util::vartime_msm_slices(&self.n, &n[..self.n.len()], util::MSM_CHUNK_VT);
        if check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// `self += w t` (batch verification).
    pub(crate) fn add_scaled(&mut self, w: Scalar, t: Terms) {
        self.g += w * t.g;
        for (v, x) in [(&mut self.h, &t.h), (&mut self.n, &t.n)] {
            if v.len() < x.len() {
                v.resize(x.len(), Scalar::ZERO);
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

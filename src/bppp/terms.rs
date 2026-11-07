//! A verification equation as a linear combination over the generators, checked by one
//! multiscalar multiplication (spec §2.4, §3.7) or accumulated for batch verification (§3.11).

use alloc::vec;
use alloc::vec::Vec;
use core::iter::once;

use ff::Field as _;
use group::Group;

use super::gens::BpppGens;
use crate::curve::Curve;
use crate::errors::ProofError;

/// `g G + <h, H> + <n, N> + sum k P = 0` over the generators `G`, `H`, `N` and the proof's own
/// points `P` (shorter `h`, `n` are zero-padded).
pub(crate) struct Terms<C: Curve> {
    pub(crate) g: C::Scalar,
    pub(crate) h: Vec<C::Scalar>,
    pub(crate) n: Vec<C::Scalar>,
    pub(crate) points: Vec<(C::Scalar, C::Point)>,
}

/// The equation holds iff the sum is the identity.
fn verdict<P: Group>(sum: P) -> Result<(), ProofError> {
    if bool::from(sum.is_identity()) {
        Ok(())
    } else {
        Err(ProofError::VerificationError)
    }
}

impl<C: Curve> Default for Terms<C> {
    fn default() -> Self {
        Terms { g: C::Scalar::ZERO, h: Vec::new(), n: Vec::new(), points: Vec::new() }
    }
}

impl<C: Curve> Terms<C> {
    /// Over the generators of [`BpppGens`]: with the cached table of `h[1..] || n` when the
    /// multiplication is small enough to gain from it (`Curve::TABLE_CROSSOVER`) and the table
    /// is of these very generators.
    pub(crate) fn check(&self, gens: &BpppGens<C>) -> Result<(), ProofError> {
        match self.with_table(gens) {
            Some(sum) => verdict(sum),
            None => self.check_with(&gens.g, &gens.h, gens.n),
        }
    }

    fn with_table(&self, gens: &BpppGens<C>) -> Option<C::Point> {
        // G, H_0 and the proof's points are not in the table
        if self.h.len() > gens.h.len() || self.n.len() > gens.n.len() {
            return None;
        }
        let table = gens.table(2 + self.points.len())?;
        let (nh, nn) = (gens.h.len() - 1, gens.n.len());
        let mut s = vec![C::Scalar::ZERO; nh + nn];
        for (x, y) in s.iter_mut().zip(self.h.iter().skip(1)) {
            *x = *y;
        }
        s[nh..nh + self.n.len()].copy_from_slice(&self.n);
        let h0 = self.h.first().copied().unwrap_or(C::Scalar::ZERO);
        let ds: Vec<C::Scalar> = once(self.g).chain(once(h0)).chain(self.points.iter().map(|(k, _)| *k)).collect();
        let dp: Vec<C::Point> = once(gens.g).chain(once(gens.h[0])).chain(self.points.iter().map(|(_, p)| *p)).collect();
        Some(table.msm(&s, &ds, &dp))
    }

    /// Over the generators `g`, `h`, `n` (at least as long as the coefficients); public
    /// scalars, variable time.
    pub(crate) fn check_with(&self, g: &C::Point, h: &[C::Point], n: &[C::Point]) -> Result<(), ProofError> {
        let ks: Vec<C::Scalar> = once(self.g).chain(self.points.iter().map(|(k, _)| *k)).collect();
        let ps: Vec<C::Point> = once(*g).chain(self.points.iter().map(|(_, p)| *p)).collect();
        verdict(C::msm_vt(&ks, &ps) + C::msm_vt(&self.h, &h[..self.h.len()]) + C::msm_vt(&self.n, &n[..self.n.len()]))
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

//! Compact storage of linear constraints for the prover and the verifier.
//!
//! A `LinearCombination` term is a `(Variable, Scalar)` pair of 48 bytes in its own heap
//! vector. Both sides need the constraints only once, to flatten them with powers of the
//! challenge `z`, so each term is stored as 8 bytes: a packed variable and an index into a
//! table of distinct coefficients (circuits use few distinct coefficients: ±1, powers of
//! two, challenge powers). The prover does not use constant terms and drops them; the
//! verifier keeps them. Coefficients ±1 (most terms) are flattened without a multiplication.

#![allow(non_snake_case)]

use std::collections::HashMap;

use curve25519_dalek::scalar::Scalar;

use super::{LinearCombination, Variable};

const TAG_SHIFT: u32 = 29;
const INDEX_MASK: u32 = (1 << TAG_SHIFT) - 1;
const TAG_LEFT: u32 = 0;
const TAG_RIGHT: u32 = 1;
const TAG_OUTPUT: u32 = 2;
const TAG_COMMITTED: u32 = 3;
const TAG_ONE: u32 = 4;
/// Indices of the pre-seeded coefficients.
const COEFF_ONE: u32 = 0;
const COEFF_MINUS_ONE: u32 = 1;

/// The flattened constraint weights `(wL, wR, wO, wV, wc)`.
pub(super) type Flattened = (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar);

pub(super) struct ConstraintStore {
    keep_constants: bool,
    /// `(packed variable, coefficient index)` for all terms of all constraints.
    terms: Vec<(u32, u32)>,
    /// End offset (exclusive) into `terms` of each constraint.
    ends: Vec<usize>,
    coeffs: Vec<Scalar>,
    index: HashMap<[u8; 32], u32>,
}

impl ConstraintStore {
    pub(super) fn new(keep_constants: bool) -> Self {
        let coeffs = vec![Scalar::ONE, -Scalar::ONE];
        let index = coeffs.iter().enumerate().map(|(i, c)| (c.to_bytes(), i as u32)).collect();
        ConstraintStore { keep_constants, terms: Vec::new(), ends: Vec::new(), coeffs, index }
    }

    pub(super) fn len(&self) -> usize {
        self.ends.len()
    }

    pub(super) fn push(&mut self, lc: &LinearCombination) {
        for (var, coeff) in &lc.terms {
            let packed = match *var {
                Variable::MultiplierLeft(i) => pack(TAG_LEFT, i),
                Variable::MultiplierRight(i) => pack(TAG_RIGHT, i),
                Variable::MultiplierOutput(i) => pack(TAG_OUTPUT, i),
                Variable::Committed(i) => pack(TAG_COMMITTED, i),
                Variable::One() if self.keep_constants => pack(TAG_ONE, 0),
                Variable::One() => continue,
            };
            // ±1 (most terms) without hashing; plain byte comparison of public values.
            let bytes = coeff.as_bytes();
            let c = if bytes == self.coeffs[COEFF_ONE as usize].as_bytes() {
                COEFF_ONE
            } else if bytes == self.coeffs[COEFF_MINUS_ONE as usize].as_bytes() {
                COEFF_MINUS_ONE
            } else {
                let next = self.coeffs.len() as u32;
                let c = *self.index.entry(coeff.to_bytes()).or_insert(next);
                if c == next {
                    self.coeffs.push(*coeff);
                }
                c
            };
            self.terms.push((packed, c));
        }
        self.ends.push(self.terms.len());
    }

    /// $w_X[i] = \sum_q z^{q+1} W_X[q][i]$ for the multiplier columns, $-\ldots$ for the
    /// committed column and the constant (zero if constants are not kept); frees the storage.
    ///
    /// With `parallel`, every thread owns a range of variable indices and scans all terms,
    /// recomputing the powers of `z` itself: no extra memory, and each sum is accumulated in
    /// the same order as in the serial code.
    pub(super) fn flatten(&mut self, z: &Scalar, n: usize, m: usize) -> Flattened {
        let mut wL = vec![Scalar::ZERO; n];
        let mut wR = vec![Scalar::ZERO; n];
        let mut wO = vec![Scalar::ZERO; n];
        let mut wV = vec![Scalar::ZERO; m];
        let mut wc = Scalar::ZERO;

        // Scan all terms; `apply(tag, i, t)` gets every term with t = z^{q+1} * coeff.
        let scan = |apply: &mut dyn FnMut(u32, usize, Scalar), wanted: &dyn Fn(u32, usize) -> bool| {
            let mut exp_z = *z;
            let mut start = 0;
            for &end in &self.ends {
                for &(packed, c) in &self.terms[start..end] {
                    let (tag, i) = (packed >> TAG_SHIFT, (packed & INDEX_MASK) as usize);
                    if !wanted(tag, i) {
                        continue;
                    }
                    let t = match c {
                        COEFF_ONE => exp_z,
                        COEFF_MINUS_ONE => -exp_z,
                        _ => exp_z * self.coeffs[c as usize],
                    };
                    apply(tag, i, t);
                }
                start = end;
                exp_z *= z;
            }
        };
        let multiplier_part = |lo: usize, wl: &mut [Scalar], wr: &mut [Scalar], wo: &mut [Scalar]| {
            let hi = lo + wl.len();
            scan(
                &mut |tag, i, t| match tag {
                    TAG_LEFT => wl[i - lo] += t,
                    TAG_RIGHT => wr[i - lo] += t,
                    _ => wo[i - lo] += t,
                },
                &|tag, i| tag <= TAG_OUTPUT && lo <= i && i < hi,
            );
        };
        let other_part = |wv: &mut [Scalar], wc: &mut Scalar| {
            scan(
                &mut |tag, i, t| match tag {
                    TAG_COMMITTED => wv[i] -= t,
                    _ => *wc -= t,
                },
                &|tag, _| tag >= TAG_COMMITTED,
            );
        };

        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            let part = (n + rayon::current_num_threads() - 1) / rayon::current_num_threads();
            let part = part.max(1);
            rayon::join(
                || {
                    wL.par_chunks_mut(part)
                        .zip(wR.par_chunks_mut(part))
                        .zip(wO.par_chunks_mut(part))
                        .enumerate()
                        .for_each(|(k, ((wl, wr), wo))| multiplier_part(k * part, wl, wr, wo))
                },
                || other_part(&mut wV, &mut wc),
            );
        }
        #[cfg(not(feature = "parallel"))]
        {
            let _ = (&multiplier_part, &other_part);
            scan(
                &mut |tag, i, t| match tag {
                    TAG_LEFT => wL[i] += t,
                    TAG_RIGHT => wR[i] += t,
                    TAG_OUTPUT => wO[i] += t,
                    TAG_COMMITTED => wV[i] -= t,
                    _ => wc -= t,
                },
                &|_, _| true,
            );
        }

        *self = ConstraintStore::new(self.keep_constants);
        (wL, wR, wO, wV, wc)
    }
}

impl ConstraintStore {
    /// The terms of constraint `q`, decoded (constants appear only if they are kept).
    #[cfg(feature = "bppp")]
    pub(super) fn row(&self, q: usize) -> impl Iterator<Item = (Variable, Scalar)> + '_ {
        let start = if q == 0 { 0 } else { self.ends[q - 1] };
        self.terms[start..self.ends[q]].iter().map(move |&(packed, c)| {
            let i = (packed & INDEX_MASK) as usize;
            let var = match packed >> TAG_SHIFT {
                TAG_LEFT => Variable::MultiplierLeft(i),
                TAG_RIGHT => Variable::MultiplierRight(i),
                TAG_OUTPUT => Variable::MultiplierOutput(i),
                TAG_COMMITTED => Variable::Committed(i),
                _ => Variable::One(),
            };
            (var, self.coeffs[c as usize])
        })
    }
}

fn pack(tag: u32, i: usize) -> u32 {
    assert!(i <= INDEX_MASK as usize, "too many variables for the compact constraint store");
    tag << TAG_SHIFT | i as u32
}

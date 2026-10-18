//! Compact storage of linear constraints for the prover.
//!
//! A `LinearCombination` term is a `(Variable, Scalar)` pair of 48 bytes in its own heap
//! vector. The prover only needs the constraints once, to flatten them with powers of the
//! challenge `z`, so it stores each term as 8 bytes: a packed variable and an index into a
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
            let next = self.coeffs.len() as u32;
            let c = *self.index.entry(coeff.to_bytes()).or_insert(next);
            if c == next {
                self.coeffs.push(*coeff);
            }
            self.terms.push((packed, c));
        }
        self.ends.push(self.terms.len());
    }

    /// $w_X[i] = \sum_q z^{q+1} W_X[q][i]$ for the multiplier columns, $-\ldots$ for the
    /// committed column and the constant (zero if constants are not kept); frees the storage.
    pub(super) fn flatten(&mut self, z: &Scalar, n: usize, m: usize) -> Flattened {
        let mut w = [vec![Scalar::ZERO; n], vec![Scalar::ZERO; n], vec![Scalar::ZERO; n], vec![Scalar::ZERO; m]];
        let mut wc = Scalar::ZERO;
        let mut exp_z = *z;
        let mut start = 0;
        for &end in &self.ends {
            for &(packed, c) in &self.terms[start..end] {
                let (tag, i) = (packed >> TAG_SHIFT, (packed & INDEX_MASK) as usize);
                let t = match c {
                    COEFF_ONE => exp_z,
                    COEFF_MINUS_ONE => -exp_z,
                    _ => exp_z * self.coeffs[c as usize],
                };
                match tag {
                    TAG_COMMITTED => w[3][i] -= t,
                    TAG_ONE => wc -= t,
                    _ => w[tag as usize][i] += t,
                }
            }
            start = end;
            exp_z *= z;
        }
        *self = ConstraintStore::new(self.keep_constants);
        let [wL, wR, wO, wV] = w;
        (wL, wR, wO, wV, wc)
    }
}

fn pack(tag: u32, i: usize) -> u32 {
    assert!(i <= INDEX_MASK as usize, "too many variables for the compact constraint store");
    tag << TAG_SHIFT | i as u32
}

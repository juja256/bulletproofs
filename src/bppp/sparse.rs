//! Sparse matrices for circuit constraints.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::scalar::Scalar;
use sha3::{Digest, Sha3_256};

/// A matrix stored by rows: row `r` holds the `(column, coefficient)` terms
/// `start[r]..start[r + 1]`, in the order they were pushed.
#[derive(Clone, Debug, PartialEq)]
pub struct SparseMatrix {
    n_cols: usize,
    start: Vec<usize>,
    cols: Vec<u32>,
    vals: Vec<Scalar>,
}

impl SparseMatrix {
    /// An empty matrix (no rows) with `n_cols` columns.
    pub fn new(n_cols: usize) -> Self {
        assert!(n_cols <= u32::MAX as usize, "too many columns");
        SparseMatrix { n_cols, start: vec![0], cols: Vec::new(), vals: Vec::new() }
    }

    /// Append a row of `(column, coefficient)` terms. Panics on a column out of range.
    pub fn push_row<I: IntoIterator<Item = (usize, Scalar)>>(&mut self, terms: I) {
        for (c, v) in terms {
            assert!(c < self.n_cols, "column {} out of range ({} columns)", c, self.n_cols);
            self.cols.push(c as u32);
            self.vals.push(v);
        }
        self.start.push(self.cols.len());
    }

    /// Append the rows of `other` (same number of columns).
    pub(crate) fn extend_rows(&mut self, other: &SparseMatrix) {
        assert_eq!(self.n_cols, other.n_cols, "column counts differ");
        let base = self.cols.len();
        self.cols.extend_from_slice(&other.cols);
        self.vals.extend_from_slice(&other.vals);
        self.start.extend(other.start[1..].iter().map(|s| base + s));
    }

    /// Number of rows.
    pub fn n_rows(&self) -> usize {
        self.start.len() - 1
    }

    /// Number of columns.
    pub fn n_cols(&self) -> usize {
        self.n_cols
    }

    /// The terms of row `r`.
    pub fn row(&self, r: usize) -> impl Iterator<Item = (usize, &Scalar)> {
        let (a, b) = (self.start[r], self.start[r + 1]);
        self.cols[a..b].iter().map(|&c| c as usize).zip(&self.vals[a..b])
    }

    /// `M x` for `x` with at least `n_cols` entries.
    pub fn mul_vec(&self, x: &[Scalar]) -> Vec<Scalar> {
        (0..self.n_rows()).map(|r| self.row(r).map(|(c, v)| v * x[c]).sum()).collect()
    }

    /// `out += y^T M`, for `y` with `n_rows` and `out` with `n_cols` entries.
    pub(crate) fn add_transposed(&self, y: &[Scalar], out: &mut [Scalar]) {
        for (r, yr) in y.iter().enumerate().take(self.n_rows()) {
            for (c, v) in self.row(r) {
                out[c] += yr * v;
            }
        }
    }

    /// Feed the rows into a circuit digest (spec §3.9).
    pub(crate) fn hash_into(&self, h: &mut Sha3_256) {
        for r in 0..self.n_rows() {
            h.update(((self.start[r + 1] - self.start[r]) as u64).to_le_bytes());
            for (c, v) in self.row(r) {
                h.update((c as u64).to_le_bytes());
                h.update(v.as_bytes());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extend_rows_appends_rows() {
        let s = |x: u64| Scalar::from(x);
        let mut a = SparseMatrix::new(3);
        a.push_row(vec![(0, s(1)), (2, s(2))]);
        let mut b = SparseMatrix::new(3);
        b.push_row(vec![]);
        b.push_row(vec![(1, s(3))]);
        let mut direct = a.clone();
        for r in 0..b.n_rows() {
            direct.push_row(b.row(r).map(|(c, v)| (c, *v)));
        }
        a.extend_rows(&b);
        assert_eq!(a, direct);
        assert_eq!(a.n_rows(), 3);
    }
}

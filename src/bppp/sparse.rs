//! Sparse matrices for circuit constraints.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::scalar::Scalar;
use sha3::{Digest, Sha3_256};

/// SHA3-256 fed through a 64 KiB buffer: the digest of the same byte stream with far fewer
/// calls into the hash (circuit digests feed it a few bytes at a time).
pub(crate) struct BufHasher {
    h: Sha3_256,
    buf: Vec<u8>,
}

impl BufHasher {
    const CAP: usize = 1 << 16;

    pub(crate) fn new() -> Self {
        BufHasher { h: Sha3_256::new(), buf: Vec::with_capacity(Self::CAP) }
    }

    pub(crate) fn update(&mut self, bytes: impl AsRef<[u8]>) {
        let b = bytes.as_ref();
        if self.buf.len() + b.len() > Self::CAP {
            self.h.update(&self.buf);
            self.buf.clear();
            if b.len() > Self::CAP {
                self.h.update(b);
                return;
            }
        }
        self.buf.extend_from_slice(b);
    }

    pub(crate) fn finalize(mut self) -> [u8; 32] {
        self.h.update(&self.buf);
        self.h.finalize().into()
    }
}

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

    /// `out += y^T M`, for `y` with `n_rows` and `out` with `n_cols` entries. With `parallel`,
    /// each thread owns a range of columns of `out` and scans all terms (no extra memory; the
    /// same sums, added in the same row order).
    pub(crate) fn add_transposed(&self, y: &[Scalar], out: &mut [Scalar]) {
        let rows = self.n_rows().min(y.len());
        let add = |lo: usize, out: &mut [Scalar]| {
            let hi = lo + out.len();
            for (r, yr) in y.iter().enumerate().take(rows) {
                for (c, v) in self.row(r) {
                    if (lo..hi).contains(&c) {
                        out[c - lo] += yr * v;
                    }
                }
            }
        };
        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            let threads = rayon::current_num_threads();
            if threads > 1 && self.vals.len() >= 1 << 14 && !out.is_empty() {
                let chunk = (out.len() + threads - 1) / threads;
                out.par_chunks_mut(chunk).enumerate().for_each(|(i, o)| add(i * chunk, o));
                return;
            }
        }
        add(0, out)
    }

    /// Feed the rows into a circuit digest (spec §3.9).
    pub(crate) fn hash_into(&self, h: &mut BufHasher) {
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

    /// `y^T M` (the parallel path above 2^14 terms) equals the direct double loop.
    #[test]
    fn add_transposed_matches_the_direct_sum() {
        use rand_chacha::rand_core::{RngCore, SeedableRng};
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let (rows, cols) = (2000usize, 301usize);
        let mut m = SparseMatrix::new(cols);
        let mut terms = Vec::new();
        for _ in 0..rows {
            let row: Vec<(usize, Scalar)> = (0..20).map(|_| ((rng.next_u32() as usize) % cols, Scalar::from(rng.next_u64()))).collect();
            terms.push(row.clone());
            m.push_row(row);
        }
        assert!(m.vals.len() >= 1 << 14);
        let y: Vec<Scalar> = (0..rows).map(|_| Scalar::from(rng.next_u64())).collect();
        let mut direct = vec![Scalar::from(7u64); cols];
        for (r, row) in terms.iter().enumerate() {
            for (c, v) in row {
                direct[*c] += y[r] * v;
            }
        }
        let mut out = vec![Scalar::from(7u64); cols];
        m.add_transposed(&y, &mut out);
        assert_eq!(out, direct);
    }

    /// The buffered hasher gives the digest of the same bytes fed directly, for pieces of
    /// every size around the buffer capacity.
    #[test]
    fn buffered_hasher_is_sha3() {
        use rand_chacha::rand_core::{RngCore, SeedableRng};
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(4);
        let (mut a, mut b) = (BufHasher::new(), Sha3_256::new());
        for len in [0usize, 1, 7, 32, 1000, (1 << 16) - 1, 1 << 16, (1 << 16) + 1, 3, 200_000, 40] {
            let mut piece = vec![0u8; len];
            rng.fill_bytes(&mut piece);
            a.update(&piece);
            b.update(&piece);
        }
        let direct: [u8; 32] = b.finalize().into();
        assert_eq!(a.finalize(), direct);
    }

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

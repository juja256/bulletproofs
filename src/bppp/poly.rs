//! Laurent polynomials in `T` for the circuit protocol (spec §3.5–3.6).

use alloc::vec::Vec;


use crate::curve::Field;

/// Lowest degree held by [`Poly`]: `n(T)` reaches `T^-1`, so `<n, n>` reaches `T^-2`.
const MIN_DEG: i32 = -2;
/// Highest degree held by [`Poly`]: the blinding polynomial reaches `T^{3+7}` (spec §3.6).
const MAX_DEG: i32 = 10;
const LEN: usize = (MAX_DEG - MIN_DEG + 1) as usize;

/// A scalar Laurent polynomial with degrees `MIN_DEG..=MAX_DEG`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Poly<F: Field>([F; LEN]);

impl<F: Field> Poly<F> {
    pub fn zero() -> Self {
        Poly([F::ZERO; LEN])
    }

    pub fn coeff(&self, d: i32) -> F {
        self.0[(d - MIN_DEG) as usize]
    }

    pub fn add(&mut self, d: i32, x: F) {
        self.0[(d - MIN_DEG) as usize] += x;
    }

    pub fn sub_poly(&mut self, o: &Poly<F>) {
        for (a, b) in self.0.iter_mut().zip(o.0.iter()) {
            *a -= b;
        }
    }
}

/// `t^d` for a possibly negative `d` (public values, variable time).
pub(crate) fn pow_signed<F: Field>(t: F, t_inv: F, d: i32) -> F {
    let (base, e) = if d >= 0 { (t, d as u64) } else { (t_inv, (-d) as u64) };
    crate::util::scalar_exp_vartime(&base, e)
}

/// A vector Laurent polynomial given by its non-zero terms `(degree, coefficients)`; terms of
/// different lengths are zero-padded.
pub(crate) struct VecPoly<F: Field>(pub Vec<(i32, Vec<F>)>);

impl<F: Field> VecPoly<F> {
    /// The value at `t`, as a vector of length `len`.
    pub fn eval(&self, t: F, t_inv: F, len: usize) -> Vec<F> {
        let terms: Vec<(F, &Vec<F>)> = self.0.iter().map(|(d, v)| (pow_signed(t, t_inv, *d), v)).collect();
        crate::util::map_index(len, |i| terms.iter().filter_map(|(x, v)| v.get(i).map(|a| *x * a)).sum())
    }

    /// `<self(T), other(T)>`, or with weights `w` (`<a, b>_w = sum a_i b_i w_i`). The weights
    /// are folded into each of `self`'s terms once (`<a, b>_w = <a w, b>`, one weighted term
    /// alive at a time); for `p.inner(p, _)` only the pairs `i <= j` are computed (the product
    /// is symmetric); the inner products run in parallel with `parallel`. Same values as the
    /// direct double sum.
    pub fn inner(&self, other: &VecPoly<F>, w: Option<&[F]>) -> Poly<F> {
        let same = core::ptr::eq(self, other);
        let mut p = Poly::zero();
        for (i, (da, a)) in self.0.iter().enumerate() {
            let weighted: Vec<F>;
            let a: &[F] = match w {
                Some(w) => {
                    weighted = a.iter().zip(w).map(|(x, w)| *x * w).collect();
                    &weighted
                }
                None => a,
            };
            for (j, (db, b)) in other.0.iter().enumerate() {
                if same && j < i {
                    continue;
                }
                let n = a.len().min(b.len());
                let x = crate::util::inner_product_par(&a[..n], &b[..n]);
                p.add(da + db, if same && j > i { x + x } else { x });
            }
        }
        p
    }
}

#[cfg(test)]
mod tests {
    use curve25519_dalek::scalar::Scalar;
    use super::*;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn direct(a: &VecPoly<Scalar>, b: &VecPoly<Scalar>, w: Option<&[Scalar]>) -> Poly<Scalar> {
        let mut p = Poly::zero();
        for (da, a) in &a.0 {
            for (db, b) in &b.0 {
                let x: Scalar = match w {
                    Some(w) => a.iter().zip(b).zip(w).map(|((x, y), w)| x * y * w).sum(),
                    None => a.iter().zip(b).map(|(x, y)| x * y).sum(),
                };
                p.add(da + db, x);
            }
        }
        p
    }

    /// The folded, symmetric, parallel inner product equals the direct double sum, for terms
    /// of different lengths and weights shorter or longer than the terms.
    #[test]
    fn inner_matches_the_direct_sum() {
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let mut v = |n: usize| (0..n).map(|_| Scalar::random(&mut rng)).collect::<Vec<_>>();
        let a = VecPoly(vec![(-1, v(7)), (0, v(5)), (2, v(9)), (3, v(1))]);
        let b = VecPoly(vec![(0, v(6)), (1, v(9)), (4, v(3))]);
        for w in [None, Some(v(9)), Some(v(4)), Some(v(12))] {
            let w = w.as_deref();
            assert_eq!(a.inner(&a, w), direct(&a, &a, w));
            assert_eq!(a.inner(&b, w), direct(&a, &b, w));
            assert_eq!(b.inner(&a, w), direct(&b, &a, w));
        }
    }
}

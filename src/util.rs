#![deny(missing_docs)]
#![allow(non_snake_case)]
// Some helpers serve only the optional R1CS and BP++ code.
#![cfg_attr(not(any(feature = "bppp", feature = "yoloproofs")), allow(dead_code))]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use clear_on_drop::clear::Clear;
use curve25519_dalek::scalar::Scalar;

use crate::inner_product_proof::inner_product;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};

/// Chunk size for constant-time multiscalar multiplication: Straus keeps a lookup table of
/// 8 points (1.3 KB) per input point, so chunking bounds the memory to a few MB. The 256
/// doublings are amortised over the chunk, so chunking costs (almost) nothing.
pub const MSM_CHUNK_CT: usize = 1 << 12;
/// Chunk size for variable-time multiscalar multiplication (Pippenger, 224 B per point;
/// the window is capped at 8 bits, so larger batches are barely faster).
pub const MSM_CHUNK_VT: usize = 1 << 14;

/// $\sum_i s_i P_i$ over slices, by chunks of `chunk` terms without copying (in parallel
/// with `parallel`). `vartime` must only be used for public scalars.
pub fn msm_slices(scalars: &[Scalar], points: &[RistrettoPoint], chunk: usize, vartime: bool) -> RistrettoPoint {
    assert_eq!(scalars.len(), points.len());
    let msm = |(s, p): (&[Scalar], &[RistrettoPoint])| {
        if vartime {
            RistrettoPoint::vartime_multiscalar_mul(s, p)
        } else {
            RistrettoPoint::multiscalar_mul(s, p)
        }
    };
    #[cfg(feature = "parallel")]
    {
        use rayon::prelude::*;
        scalars
            .par_chunks(chunk)
            .zip(points.par_chunks(chunk))
            .map(msm)
            .reduce(RistrettoPoint::identity, |a, b| a + b)
    }
    #[cfg(not(feature = "parallel"))]
    scalars.chunks(chunk).zip(points.chunks(chunk)).map(msm).fold(RistrettoPoint::identity(), |a, b| a + b)
}

/// [`msm_slices`] in variable time: for public scalars only.
pub fn vartime_msm_slices(scalars: &[Scalar], points: &[RistrettoPoint], chunk: usize) -> RistrettoPoint {
    msm_slices(scalars, points, chunk, true)
}

/// $\sum_v s_v P_v$ over `v in 0..len` with the terms given by `term(v)`, by chunks of
/// `chunk` terms (in parallel with `parallel`). Variable time: for public scalars only.
pub fn vartime_msm_index<'a, F>(len: usize, chunk: usize, term: F) -> RistrettoPoint
where
    F: Fn(usize) -> (Scalar, &'a RistrettoPoint) + Sync,
{
    msm_index(len, chunk, true, term)
}

/// [`vartime_msm_index`], constant time unless `vartime`.
pub fn msm_index<'a, F>(len: usize, chunk: usize, vartime: bool, term: F) -> RistrettoPoint
where
    F: Fn(usize) -> (Scalar, &'a RistrettoPoint) + Sync,
{
    let run = |c: usize| {
        let (start, end) = (c * chunk, ((c + 1) * chunk).min(len));
        let (s, p): (Vec<Scalar>, Vec<&RistrettoPoint>) = (start..end).map(&term).unzip();
        if vartime {
            RistrettoPoint::vartime_multiscalar_mul(s, p)
        } else {
            RistrettoPoint::multiscalar_mul(s, p)
        }
    };
    let chunks = (len + chunk - 1) / chunk;
    #[cfg(feature = "parallel")]
    {
        use rayon::prelude::*;
        (0..chunks).into_par_iter().map(run).reduce(RistrettoPoint::identity, |a, b| a + b)
    }
    #[cfg(not(feature = "parallel"))]
    (0..chunks).map(run).fold(RistrettoPoint::identity(), |a, b| a + b)
}

/// `[1, x, x^2, ..., x^(len-1)]`, by chunks (in parallel with `parallel`).
pub fn powers(x: Scalar, len: usize) -> Vec<Scalar> {
    const CHUNK: usize = 1 << 12;
    let chunks = map_index((len + CHUNK - 1) / CHUNK, |c| {
        let start = c * CHUNK;
        let mut p = scalar_exp_vartime(&x, start as u64);
        let end = (start + CHUNK).min(len);
        let mut out = Vec::with_capacity(end - start);
        for _ in start..end {
            out.push(p);
            p *= x;
        }
        out
    });
    chunks.concat()
}

/// `<a, b>`, by chunks (in parallel with `parallel`).
pub fn inner_product_par(a: &[Scalar], b: &[Scalar]) -> Scalar {
    const CHUNK: usize = 1 << 14;
    assert_eq!(a.len(), b.len());
    map_index((a.len() + CHUNK - 1) / CHUNK, |c| {
        let r = c * CHUNK..((c + 1) * CHUNK).min(a.len());
        inner_product(&a[r.clone()], &b[r])
    })
    .into_iter()
    .sum()
}

/// `for i in 0..n { consume(build(i)) }`, with `build` in parallel (with `parallel`) in waves
/// of a few items per thread, so that at most one wave of results is held at a time; `consume`
/// sees the results in order.
pub fn map_in_order<T: Send, F: Fn(usize) -> T + Sync + Send>(n: usize, build: F, mut consume: impl FnMut(T)) {
    #[cfg(feature = "parallel")]
    let wave = 4 * rayon::current_num_threads();
    #[cfg(not(feature = "parallel"))]
    let wave = 1;
    let mut start = 0;
    while start < n {
        let len = wave.min(n - start);
        for t in map_index(len, |j| build(start + j)) {
            consume(t);
        }
        start += len;
    }
}

/// `(0..n).map(f).collect()`, in parallel with `parallel`.
pub fn map_index<T: Send, F: Fn(usize) -> T + Sync + Send>(n: usize, f: F) -> Vec<T> {
    #[cfg(feature = "parallel")]
    {
        use rayon::prelude::*;
        (0..n).into_par_iter().map(f).collect()
    }
    #[cfg(not(feature = "parallel"))]
    (0..n).map(f).collect()
}


/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<Scalar>, pub Vec<Scalar>);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2(pub Scalar, pub Scalar, pub Scalar);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[cfg(feature = "yoloproofs")]
pub struct Poly6 {
    pub t1: Scalar,
    pub t2: Scalar,
    pub t3: Scalar,
    pub t4: Scalar,
    pub t5: Scalar,
    pub t6: Scalar,
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::ONE;
    ScalarExp { x, next_exp_x }
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.len() != b.len() {
        // throw some error
        //println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![Scalar::ZERO; b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![Scalar::ZERO; n], vec![Scalar::ZERO; n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1) -> Poly2 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::ZERO; n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

impl Poly2 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        self.0 + x * (self.1 + x * self.2)
    }
}

#[cfg(feature = "yoloproofs")]
impl Poly6 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

impl Drop for VecPoly1 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.clear();
        }
        for e in self.1.iter_mut() {
            e.clear();
        }
    }
}

impl Drop for Poly2 {
    fn drop(&mut self) {
        self.0.clear();
        self.1.clear();
        self.2.clear();
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for Poly6 {
    fn drop(&mut self) {
        self.t1.clear();
        self.t2.clear();
        self.t3.clear();
        self.t4.clear();
        self.t5.clear();
        self.t6.clear();
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a consttime version of this would be awfully similar to a Montgomery ladder.
pub fn scalar_exp_vartime(x: &Scalar, mut n: u64) -> Scalar {
    let mut result = Scalar::ONE;
    let mut aux = *x; // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result = result * aux;
        }
        n = n >> 1;
        aux = aux * aux; // FIXME: one unnecessary mult at the last step here!
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers(x: &Scalar, n: usize) -> Scalar {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return Scalar::from(n as u64);
    }
    let mut m = n;
    let mut result = Scalar::ONE + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m = m / 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow(x: &Scalar, n: usize) -> Scalar {
    exp_iter(*x).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from(1u64));
        assert_eq!(exp_2[1], Scalar::from(2u64));
        assert_eq!(exp_2[2], Scalar::from(4u64));
        assert_eq!(exp_2[3], Scalar::from(8u64));
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }

    /// Raises `x` to the power `n`.
    fn scalar_exp_vartime_slow(x: &Scalar, n: u64) -> Scalar {
        let mut result = Scalar::ONE;
        for _ in 0..n {
            result = result * x;
        }
        result
    }

    #[test]
    fn test_scalar_exp() {
        let x = Scalar::from_bits(
            *b"\x84\xfc\xbcOx\x12\xa0\x06\xd7\x91\xd9z:'\xdd\x1e!CE\xf7\xb1\xb9Vz\x810sD\x96\x85\xb5\x07",
        );
        assert_eq!(scalar_exp_vartime(&x, 0), Scalar::ONE);
        assert_eq!(scalar_exp_vartime(&x, 1), x);
        assert_eq!(scalar_exp_vartime(&x, 2), x * x);
        assert_eq!(scalar_exp_vartime(&x, 3), x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 4), x * x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 5), x * x * x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 64), scalar_exp_vartime_slow(&x, 64));
        assert_eq!(
            scalar_exp_vartime(&x, 0b11001010),
            scalar_exp_vartime_slow(&x, 0b11001010)
        );
    }

    #[test]
    fn test_sum_of_powers() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), sum_of_powers(&x, 0));
        assert_eq!(sum_of_powers_slow(&x, 1), sum_of_powers(&x, 1));
        assert_eq!(sum_of_powers_slow(&x, 2), sum_of_powers(&x, 2));
        assert_eq!(sum_of_powers_slow(&x, 4), sum_of_powers(&x, 4));
        assert_eq!(sum_of_powers_slow(&x, 8), sum_of_powers(&x, 8));
        assert_eq!(sum_of_powers_slow(&x, 16), sum_of_powers(&x, 16));
        assert_eq!(sum_of_powers_slow(&x, 32), sum_of_powers(&x, 32));
        assert_eq!(sum_of_powers_slow(&x, 64), sum_of_powers(&x, 64));
    }

    #[test]
    fn test_sum_of_powers_slow() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), Scalar::ZERO);
        assert_eq!(sum_of_powers_slow(&x, 1), Scalar::ONE);
        assert_eq!(sum_of_powers_slow(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow(&x, 6), Scalar::from(111111u64));
    }

    #[test]
    fn vec_of_scalars_clear_on_drop() {
        let mut v = vec![Scalar::from(24u64), Scalar::from(42u64)];

        for e in v.iter_mut() {
            e.clear();
        }

        fn flat_slice<T>(x: &[T]) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x.as_ptr() as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(flat_slice(&v.as_slice()), &[0u8; 64][..]);
        assert_eq!(v[0], Scalar::ZERO);
        assert_eq!(v[1], Scalar::ZERO);
    }

    #[test]
    fn tuple_of_scalars_clear_on_drop() {
        let mut v = Poly2(
            Scalar::from(24u64),
            Scalar::from(42u64),
            Scalar::from(255u64),
        );

        v.0.clear();
        v.1.clear();
        v.2.clear();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(as_bytes(&v), &[0u8; 96][..]);
        assert_eq!(v.0, Scalar::ZERO);
        assert_eq!(v.1, Scalar::ZERO);
        assert_eq!(v.2, Scalar::ZERO);
    }
}

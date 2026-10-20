//! Variable-time multiscalar multiplication on secp256k1 (Pippenger's bucket method with signed
//! digits): for public scalars only.

use alloc::vec;
use alloc::vec::Vec;

use k256::elliptic_curve::group::{Curve as _, Group};
use k256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use k256::{AffinePoint, EncodedPoint, FieldElement, ProjectivePoint, Scalar};

use super::Field;

/// Below this many terms the bucket method does not pay off.
const NAIVE_MAX: usize = 32;

/// The window width minimising `windows * (n + 2^(c+1))`: about one affine addition per point
/// into the buckets, and two projective additions (about twice as expensive) per bucket in the
/// running sums over `2^(c-1)` buckets.
fn window(n: usize) -> usize {
    (4..=16usize).min_by_key(|&c| (256 / c + 2) * (n + (2 << c))).unwrap()
}

/// The scalar as signed base-`2^c` digits in `[-2^(c-1), 2^(c-1))`, least significant first;
/// `256 / c + 2` digits (room for the final carry).
pub(crate) fn digits(x: &Scalar, c: usize) -> Vec<i32> {
    let be = x.to_bytes32();
    let limbs: [u64; 4] = core::array::from_fn(|k| {
        let mut b = [0u8; 8];
        b.copy_from_slice(&be[24 - 8 * k..32 - 8 * k]);
        u64::from_be_bytes(b)
    });
    let bits = |pos: usize| -> u64 {
        let (l, sh) = (pos / 64, pos % 64);
        if l >= 4 {
            return 0;
        }
        let mut v = limbs[l] >> sh;
        if sh + c > 64 && l + 1 < 4 {
            v |= limbs[l + 1] << (64 - sh);
        }
        v & ((1u64 << c) - 1)
    };
    let (full, half) = (1i64 << c, 1i64 << (c - 1));
    let mut carry = 0i64;
    (0..256 / c + 2)
        .map(|w| {
            let mut d = bits(w * c) as i64 + carry;
            carry = 0;
            if d >= half {
                d -= full;
                carry = 1;
            }
            d as i32
        })
        .collect()
}

/// `sum s_i P_i` in variable time (windows in parallel with `parallel`).
pub(crate) fn msm(s: &[Scalar], p: &[ProjectivePoint]) -> ProjectivePoint {
    assert_eq!(s.len(), p.len());
    let n = s.len();
    if n < NAIVE_MAX {
        // k256's Straus with GLV: the doublings shared by the few terms
        use k256::elliptic_curve::ops::LinearCombinationExt;
        let pairs: Vec<(ProjectivePoint, Scalar)> = p.iter().copied().zip(s.iter().copied()).collect();
        return ProjectivePoint::lincomb_ext(&pairs[..]);
    }
    msm_window(s, p, window(n))
}

/// An affine point as field elements of magnitude 1 (k256's lazily reduced representation:
/// every operand of a subtraction must have magnitude 1, hence the `normalize_weak` calls).
#[derive(Clone, Copy)]
struct Xy {
    x: FieldElement,
    y: FieldElement,
}

impl Xy {
    fn from_affine(a: &AffinePoint) -> Option<Xy> {
        let e = a.to_encoded_point(false);
        let (x, y) = (e.x()?, e.y()?);
        Some(Xy { x: FieldElement::from_bytes(x).unwrap(), y: FieldElement::from_bytes(y).unwrap() })
    }

    fn to_projective(self) -> ProjectivePoint {
        let e = EncodedPoint::from_affine_coordinates(&self.x.normalize().to_bytes(), &self.y.normalize().to_bytes(), false);
        ProjectivePoint::from(AffinePoint::from_encoded_point(&e).unwrap())
    }

    fn neg(self) -> Xy {
        Xy { x: self.x, y: self.y.negate(1).normalize_weak() }
    }
}

/// Sums the points of each bucket by rounds of pairwise affine additions, all denominators of
/// a round inverted at once (Montgomery's trick). `pts[start[b]..start[b + 1]]` are the points
/// of bucket `b`; returns the sum of each bucket.
fn bucket_sums(mut pts: Vec<Xy>, mut start: Vec<usize>) -> Vec<ProjectivePoint> {
    let buckets = start.len() - 1;
    let mut extra = vec![ProjectivePoint::IDENTITY; buckets];
    let mut den: Vec<FieldElement> = Vec::new();
    let mut prefix: Vec<FieldElement> = Vec::new();
    loop {
        // pairs (lo, lo + 1) of every bucket with two or more points left
        den.clear();
        let mut pairs = 0;
        for b in 0..buckets {
            let (lo, hi) = (start[b], start[b + 1]);
            let mut k = lo;
            while k + 1 < hi {
                den.push((pts[k + 1].x - &pts[k].x).normalize_weak());
                k += 2;
            }
            pairs += (hi - lo) / 2;
        }
        if pairs == 0 {
            break;
        }
        // invert the non-zero denominators; a zero one is P + P or P - P, done projectively
        prefix.clear();
        let mut acc = FieldElement::ONE;
        for d in &den {
            prefix.push(acc);
            if !bool::from(d.normalizes_to_zero()) {
                acc = acc * d;
            }
        }
        let mut inv = acc.invert().unwrap();
        for (d, p) in den.iter_mut().zip(&prefix).rev() {
            if !bool::from(d.normalizes_to_zero()) {
                let next = inv * &*d;
                *d = inv * p;
                inv = next;
            }
        }
        let mut out = Vec::with_capacity(pts.len() - pairs);
        let mut new_start = Vec::with_capacity(buckets + 1);
        let mut q = 0;
        for b in 0..buckets {
            new_start.push(out.len());
            let (lo, hi) = (start[b], start[b + 1]);
            let mut k = lo;
            while k + 1 < hi {
                let (p1, p2, d) = (pts[k], pts[k + 1], den[q]);
                q += 1;
                k += 2;
                if bool::from(d.normalizes_to_zero()) {
                    // x1 = x2: P2 = P1 (a doubling) or P2 = -P1 (the identity)
                    if bool::from((p2.y - &p1.y).normalize_weak().normalizes_to_zero()) {
                        extra[b] += p1.to_projective().double();
                    }
                    continue;
                }
                let lambda = (p2.y - &p1.y) * &d;
                let x3 = (lambda.square() - &p1.x - &p2.x).normalize_weak();
                let y3 = ((p1.x - &x3) * &lambda - &p1.y).normalize_weak();
                out.push(Xy { x: x3, y: y3 });
            }
            if k < hi {
                out.push(pts[k]);
            }
        }
        new_start.push(out.len());
        pts = out;
        start = new_start;
    }
    (0..buckets)
        .map(|b| match start[b] < start[b + 1] {
            true => extra[b] + pts[start[b]].to_projective(),
            false => extra[b],
        })
        .collect()
}

/// [`msm`] with the window width `c`.
pub(crate) fn msm_window(s: &[Scalar], p: &[ProjectivePoint], c: usize) -> ProjectivePoint {
    let n = s.len();
    let w = 256 / c + 2;
    let nb = 1usize << (c - 1);
    // window-major: digits[j * n + i] is digit j of scalar i
    let mut digits_t = vec![0i32; w * n];
    for (i, x) in s.iter().enumerate() {
        for (j, d) in digits(x, c).into_iter().enumerate() {
            digits_t[j * n + i] = d;
        }
    }
    // k256 0.13's batch_normalize compares an unnormalized z with zero limb by limb, so an
    // identity computed by arithmetic (q - q) would reach its batch inversion and panic: the
    // identities go in as the constant
    let p: Vec<ProjectivePoint> = p
        .iter()
        .map(|q| if bool::from(q.is_identity()) { ProjectivePoint::IDENTITY } else { *q })
        .collect();
    let mut affine = vec![AffinePoint::IDENTITY; n];
    ProjectivePoint::batch_normalize(&p, &mut affine);
    let xy: Vec<Option<Xy>> = affine.iter().map(Xy::from_affine).collect();
    let window_sum = |j: usize| {
        let d = &digits_t[j * n..(j + 1) * n];
        // counting sort of the points by bucket, the sign applied
        let mut start = vec![0usize; nb + 1];
        for (&d, p) in d.iter().zip(&xy) {
            if d != 0 && p.is_some() {
                start[d.unsigned_abs() as usize] += 1;
            }
        }
        for b in 0..nb {
            start[b + 1] += start[b];
        }
        let mut fill = start.clone();
        let mut pts = vec![Xy { x: FieldElement::ZERO, y: FieldElement::ZERO }; start[nb]];
        for (&d, p) in d.iter().zip(&xy) {
            if let (true, Some(p)) = (d != 0, p) {
                let b = d.unsigned_abs() as usize - 1;
                pts[fill[b]] = if d > 0 { *p } else { p.neg() };
                fill[b] += 1;
            }
        }
        let sums = bucket_sums(pts, start);
        // sum_k k * B_k by running sums
        let (mut run, mut sum) = (ProjectivePoint::IDENTITY, ProjectivePoint::IDENTITY);
        for b in sums.iter().rev() {
            run += b;
            sum += run;
        }
        sum
    };
    let sums = crate::util::map_index(w, window_sum);
    sums.iter().rev().fold(ProjectivePoint::IDENTITY, |acc, s| {
        let mut acc = acc;
        for _ in 0..c {
            acc = acc.double();
        }
        acc + s
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use k256::elliptic_curve::group::Group;
    use k256::elliptic_curve::Field as _;
    use k256::{ProjectivePoint, Scalar};
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// At the window boundaries, with zero, -1, repeated scalars and identity points.
    #[test]
    fn pippenger_matches_naive() {
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        for n in [0usize, 1, 2, 31, 32, 33, 257, 1000, 5000] {
            let mut s: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let mut p: Vec<ProjectivePoint> = (0..n).map(|_| ProjectivePoint::random(&mut rng)).collect();
            if n > 5 {
                s[0] = Scalar::ZERO;
                s[1] = -Scalar::ONE;
                s[2] = s[3];
                s[4] = Scalar::ONE;
                p[5] = ProjectivePoint::IDENTITY;
            }
            if n > 12 {
                // the same point twice in one bucket (a doubling) and cancelling (P - P)
                p[7] = p[6];
                s[7] = s[6];
                p[9] = p[8];
                s[9] = -s[8];
                p[11] = -p[10];
                s[11] = s[10];
            }
            let naive: ProjectivePoint = s.iter().zip(&p).map(|(s, p)| p * s).sum();
            assert_eq!(msm(&s, &p), naive, "n = {}", n);
        }
    }

    /// Times per term at 2^14 for the window widths around the chosen one (`--ignored`).
    #[test]
    #[ignore]
    fn window_widths() {
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let n = 1 << 14;
        let s: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let p: Vec<ProjectivePoint> = (0..n).map(|_| ProjectivePoint::random(&mut rng)).collect();
        for c in 9..=14 {
            let t = std::time::Instant::now();
            for _ in 0..5 {
                msm_window(&s, &p, c);
            }
            println!("c = {} (chosen {}): {:.2} us/term", c, window(n), t.elapsed().as_secs_f64() * 1e6 / 5.0 / n as f64);
        }
    }

    /// Identities computed by arithmetic (`q - q`, `q * 0`; k256's `batch_normalize` mistakes
    /// their unnormalized z for non-zero) are inputs like any other.
    #[test]
    fn computed_identities_are_inputs() {
        let mut rng = ChaCha20Rng::seed_from_u64(6);
        for n in [5usize, 40, 300] {
            let s: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let mut p: Vec<ProjectivePoint> = (0..n).map(|_| ProjectivePoint::random(&mut rng)).collect();
            let q = ProjectivePoint::random(&mut rng);
            p[0] = q - q;
            p[1] = q * Scalar::ZERO;
            p[2] = q + (-q);
            let naive: ProjectivePoint = s.iter().zip(&p).map(|(s, p)| p * s).sum();
            assert_eq!(msm(&s, &p), naive, "n = {}", n);
        }
    }

    /// Signed digits recompose the scalar for every window width.
    #[test]
    fn signed_digits_recompose() {
        let mut rng = ChaCha20Rng::seed_from_u64(4);
        let mut xs: Vec<Scalar> = (0..20).map(|_| Scalar::random(&mut rng)).collect();
        xs.extend([Scalar::ZERO, Scalar::ONE, -Scalar::ONE, -Scalar::from(2u64)]);
        for c in 2..=16 {
            for x in &xs {
                let d = digits(x, c);
                let base = Scalar::from(1u64 << c);
                let back = d.iter().rev().fold(Scalar::ZERO, |acc, &d| {
                    let d = if d < 0 { -Scalar::from((-d) as u64) } else { Scalar::from(d as u64) };
                    acc * base + d
                });
                assert_eq!(back, *x, "c = {}", c);
                assert!(d.iter().all(|&d| d >= -(1 << (c - 1)) && d <= 1 << (c - 1)));
            }
        }
    }
}

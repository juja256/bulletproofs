//! Variable-time multiscalar multiplication on secp256k1 with precomputed tables for fixed
//! points (Straus with width-`w` NAF digits; one chain of doublings for all points): for
//! public scalars only.

use alloc::vec::Vec;

use k256::elliptic_curve::group::Curve as _;
use k256::{AffinePoint, ProjectivePoint, Scalar};

use super::Field;

/// NAF width of the fixed points: tables of `2^(W_FIXED - 2)` odd multiples, in affine
/// coordinates (mixed additions).
const W_FIXED: usize = 7;
/// NAF width of the other points, whose tables are built per call.
const W_OTHER: usize = 5;
/// Digits of a width-`w` NAF: the carry out of the top bit needs up to `w` more positions.
const NAF_LEN: usize = 256 + W_FIXED + 1;

/// The odd multiples `P, 3P, ..., (2^(W_FIXED - 1) - 1) P` of every fixed point, point after
/// point.
pub struct Table {
    odd: Vec<AffinePoint>,
}

impl core::fmt::Debug for Table {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Table {{ points: {} }}", self.odd.len() >> (W_FIXED - 2))
    }
}

/// The odd multiples `P, 3P, ...` of `p`, `count` of them.
fn odd_multiples(p: &ProjectivePoint, count: usize) -> impl Iterator<Item = ProjectivePoint> {
    let two = p.double();
    core::iter::successors(Some(*p), move |x| Some(x + &two)).take(count)
}

pub(crate) fn table(p: &[ProjectivePoint]) -> Table {
    let count = 1 << (W_FIXED - 2);
    let proj: Vec<ProjectivePoint> = p.iter().flat_map(|x| odd_multiples(x, count)).collect();
    let mut odd = alloc::vec![AffinePoint::IDENTITY; proj.len()];
    // k256 fails on an empty batch
    if !proj.is_empty() {
        ProjectivePoint::batch_normalize(&proj, &mut odd);
    }
    Table { odd }
}

/// `x` as width-`w` NAF digits, least significant first: every non-zero digit is odd, below
/// `2^(w-1)` in absolute value, and followed by at least `w - 1` zeros.
pub(crate) fn naf(x: &Scalar, w: usize) -> [i8; NAF_LEN] {
    let be = x.to_bytes32();
    // little-endian limbs, two zero limbs above for the windows past the top
    let mut limbs = [0u64; 6];
    for (k, l) in limbs.iter_mut().take(4).enumerate() {
        let mut b = [0u8; 8];
        b.copy_from_slice(&be[24 - 8 * k..32 - 8 * k]);
        *l = u64::from_be_bytes(b);
    }
    let (width, mask) = (1u64 << w, (1u64 << w) - 1);
    let mut out = [0i8; NAF_LEN];
    let (mut pos, mut carry) = (0usize, 0u64);
    while pos < NAF_LEN {
        let (l, sh) = (pos / 64, pos % 64);
        let mut buf = limbs.get(l).copied().unwrap_or(0) >> sh;
        if sh + w > 64 {
            buf |= limbs.get(l + 1).copied().unwrap_or(0) << (64 - sh);
        }
        let window = carry + (buf & mask);
        if window & 1 == 0 {
            pos += 1;
            continue;
        }
        if window < width / 2 {
            carry = 0;
            out[pos] = window as i8;
        } else {
            carry = 1;
            out[pos] = (window as i64 - width as i64) as i8;
        }
        pos += w;
    }
    out
}

pub(crate) fn msm(table: &Table, s: &[Scalar], ds: &[Scalar], dp: &[ProjectivePoint]) -> ProjectivePoint {
    let per = 1 << (W_FIXED - 2);
    assert_eq!(table.odd.len(), s.len() * per);
    assert_eq!(ds.len(), dp.len());
    let fixed: Vec<[i8; NAF_LEN]> = s.iter().map(|x| naf(x, W_FIXED)).collect();
    let other: Vec<[i8; NAF_LEN]> = ds.iter().map(|x| naf(x, W_OTHER)).collect();
    let other_tables: Vec<Vec<ProjectivePoint>> = dp.iter().map(|p| odd_multiples(p, 1 << (W_OTHER - 2)).collect()).collect();
    let top = fixed.iter().chain(&other).filter_map(|d| d.iter().rposition(|x| *x != 0)).max();
    let mut acc = ProjectivePoint::IDENTITY;
    let top = match top {
        Some(t) => t,
        None => return acc,
    };
    for j in (0..=top).rev() {
        acc = acc.double();
        for (i, d) in fixed.iter().enumerate() {
            let x = d[j];
            if x > 0 {
                acc += &table.odd[i * per + (x as usize >> 1)];
            } else if x < 0 {
                acc += &-table.odd[i * per + ((-x) as usize >> 1)];
            }
        }
        for (t, d) in other_tables.iter().zip(&other) {
            let x = d[j];
            if x > 0 {
                acc += &t[x as usize >> 1];
            } else if x < 0 {
                acc -= &t[(-x) as usize >> 1];
            }
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use k256::elliptic_curve::Field as _;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// NAF digits recompose to the scalar and have the NAF shape, also for the largest
    /// scalars (the top carry).
    #[test]
    fn naf_recomposes() {
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let mut xs = alloc::vec![Scalar::ZERO, Scalar::ONE, -Scalar::ONE, -Scalar::from(2u64)];
        xs.extend((0..50).map(|_| Scalar::random(&mut rng)));
        for x in xs {
            for w in [W_OTHER, W_FIXED] {
                let d = naf(&x, w);
                let mut acc = Scalar::ZERO;
                for (j, &v) in d.iter().enumerate().rev() {
                    acc = acc.double();
                    acc += if v < 0 { -Scalar::from((-v) as u64) } else { Scalar::from(v as u64) };
                    if v != 0 {
                        assert!(v % 2 != 0 && (v.unsigned_abs() as usize) < 1 << (w - 1));
                        assert!(d[j.saturating_sub(w - 1)..j].iter().all(|z| *z == 0) || j < w - 1);
                    }
                }
                assert_eq!(acc, x);
            }
        }
    }
}

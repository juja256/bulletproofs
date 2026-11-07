//! The prime-order groups the proofs run over: ristretto255 (the default) and, with the
//! `secp256k1` feature, secp256k1.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::any::Any;
use core::fmt::Debug;

pub use ff;
pub use group;

mod ristretto;
pub use self::ristretto::Ristretto;
mod pippenger;
mod straus;
mod secp256k1;
pub use self::secp256k1::{Secp256k1, Secp256k1Compressed};

/// The scalar field of a curve, as gadgets, linear combinations and transcripts see it.
pub trait Field:
    ff::PrimeField + Copy + Debug + Default + Send + Sync + zeroize::Zeroize + serde::Serialize + serde::de::DeserializeOwned + 'static
{
    /// A uniformly random scalar from 64 uniformly random bytes (transcript challenges).
    fn from_wide(bytes: &[u8; 64]) -> Self;
    /// The canonical 32-byte encoding used in proofs and transcripts.
    fn to_bytes32(&self) -> [u8; 32];
    /// The scalar a canonical encoding gives; `None` for a value at least the field order.
    fn from_bytes32(bytes: &[u8; 32]) -> Option<Self>;
    /// Invert every entry in place (Montgomery's trick) and return the inverse of their
    /// product; the entries must be non-zero. Constant time; the partial products (secret
    /// when the entries are) are wiped.
    fn batch_invert(s: &mut [Self]) -> Self {
        use zeroize::Zeroize;
        let mut acc = Self::ONE;
        let mut prefix = alloc::vec::Vec::with_capacity(s.len());
        for x in s.iter() {
            prefix.push(acc);
            acc *= x;
        }
        let all = acc.invert().unwrap_or(Self::ZERO);
        let mut inv = all;
        for (x, p) in s.iter_mut().zip(prefix.iter()).rev() {
            let next = inv * *x;
            *x = inv * p;
            inv = next;
        }
        prefix.zeroize();
        acc.zeroize();
        inv.zeroize();
        all
    }
}

/// An encoded group element as it appears in proofs and transcripts.
///
/// The identity has an encoding: `Self::default()` (all zero bytes). One-phase R1CS proofs send
/// it for their empty second-phase commitments, and a commitment to zero with a zero blinding
/// is the identity; places where the identity is not allowed reject it with
/// [`PointEncoding::is_identity`].
pub trait PointEncoding:
    Copy + Clone + Debug + PartialEq + Eq + Default + Send + Sync + serde::Serialize + serde::de::DeserializeOwned
{
    /// The bytes of the encoding.
    fn as_bytes(&self) -> &[u8];
    /// `bytes` as an encoding (`None` for the wrong length); no curve check.
    fn from_slice(bytes: &[u8]) -> Option<Self>;
    /// Whether this is the encoding of the identity, `Self::default()`.
    fn is_identity(&self) -> bool;
}

/// A prime-order group for Bulletproofs and Bulletproofs++.
pub trait Curve: Copy + Clone + Debug + Default + PartialEq + Eq + Send + Sync + 'static {
    /// The scalar field (the group order).
    type Scalar: Field;
    /// A group element.
    type Point: group::Group<Scalar = Self::Scalar> + subtle::ConditionallySelectable + Copy + Debug + Send + Sync + zeroize::Zeroize + 'static;
    /// An encoded group element of `POINT_BYTES` bytes.
    type Compressed: PointEncoding;
    /// The name used in transcripts: `"ristretto255"`, `"secp256k1"`.
    const NAME: &'static str;
    /// Length of an encoded point.
    const POINT_BYTES: usize;

    /// The encoding of `p`; total: the identity encodes as `Compressed::default()`.
    fn compress(p: &Self::Point) -> Self::Compressed;
    /// The point `c` encodes (the identity for `Compressed::default()`); `None` if it encodes
    /// no point.
    fn decompress(c: &Self::Compressed) -> Option<Self::Point>;
    /// A point from 64 uniformly random bytes (generator derivation).
    fn point_from_uniform(bytes: &[u8; 64]) -> Self::Point;
    /// `(B, B_blinding)` of `PedersenGens::default()`.
    fn default_pedersen() -> (Self::Point, Self::Point);
    /// `sum s_i P_i` in constant time in the scalars (in parallel with `parallel`).
    fn msm_ct(s: &[Self::Scalar], p: &[Self::Point]) -> Self::Point;
    /// `sum s_i P_i` in variable time: for public scalars only.
    fn msm_vt(s: &[Self::Scalar], p: &[Self::Point]) -> Self::Point;

    /// Up to this many weighted points (fixed ones plus 3 per other point) a multiplication
    /// with tables beats [`Curve::msm_vt`] (measured); by default 0, never.
    const TABLE_CROSSOVER: usize = 0;

    /// The table of the fixed points `p` for [`Curve::msm_vt_table`]: opaque; by default the
    /// points themselves.
    fn table(p: &[Self::Point]) -> Table {
        Table::new(p.to_vec())
    }

    /// `sum s_i P_i + sum ds_j dp_j` in variable time, `P` the fixed points of `table` (made by
    /// [`Curve::table`] of this curve, as many as `s`) and `dp` other points: for public
    /// scalars only. By default [`Curve::msm_vt`] over all of them.
    fn msm_vt_table(table: &Table, s: &[Self::Scalar], ds: &[Self::Scalar], dp: &[Self::Point]) -> Self::Point {
        let p = table.get::<Vec<Self::Point>>().expect("a table of Curve::table");
        let ss: Vec<Self::Scalar> = s.iter().chain(ds).copied().collect();
        let ps: Vec<Self::Point> = p.iter().chain(dp).copied().collect();
        Self::msm_vt(&ss, &ps)
    }

    /// `sum_{v < len} s_v P_v` with the terms `term(v)`, by chunks (in parallel with
    /// `parallel`); constant time unless `vartime` (public scalars only).
    fn msm_index<'a, T>(len: usize, vartime: bool, term: T) -> Self::Point
    where
        T: Fn(usize) -> (Self::Scalar, &'a Self::Point) + Sync,
        Self::Point: 'a,
    {
        const CHUNK: usize = 1 << 12;
        crate::util::map_index((len + CHUNK - 1) / CHUNK, |c| {
            let (s, p): (alloc::vec::Vec<Self::Scalar>, alloc::vec::Vec<Self::Point>) =
                (c * CHUNK..((c + 1) * CHUNK).min(len)).map(|v| { let (s, p) = term(v); (s, *p) }).unzip();
            if vartime { Self::msm_vt(&s, &p) } else { Self::msm_ct(&s, &p) }
        })
        .into_iter()
        .fold(<Self::Point as group::Group>::identity(), |a, b| a + b)
    }
}

/// A table of fixed points made by [`Curve::table`]: opaque, each curve stores its own type.
pub struct Table(Box<dyn Any + Send + Sync>);

impl Table {
    /// Wrap a curve's table.
    pub fn new<T: Any + Send + Sync>(t: T) -> Self {
        Table(Box::new(t))
    }

    /// The table as `T`, if it is one.
    pub fn get<T: Any>(&self) -> Option<&T> {
        self.0.downcast_ref()
    }
}

impl Debug for Table {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Table")
    }
}

/// The table of fixed points (the BP++ verifier's generators, spec §3.7) of a curve.
pub(crate) struct Fixed<C: Curve> {
    table: Table,
    curve: core::marker::PhantomData<C>,
}

impl<C: Curve> Fixed<C> {
    pub(crate) fn new(points: Vec<C::Point>) -> Self {
        Fixed { table: C::table(&points), curve: core::marker::PhantomData }
    }

    /// `<s, points> + <ds, dp>` (variable time; `s` as long as the points).
    pub(crate) fn msm(&self, s: &[C::Scalar], ds: &[C::Scalar], dp: &[C::Point]) -> C::Point {
        C::msm_vt_table(&self.table, s, ds, dp)
    }
}

#[cfg(test)]
mod table_tests {
    use super::*;
    use alloc::vec::Vec;
    use ff::Field as _;
    use group::Group;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// `msm_vt_table` is `msm_vt` over the fixed and the other points, for every split,
    /// including empty parts and the scalars 0, 1 and -1.
    fn table_msm_matches_msm<C: Curve>() {
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        for (nf, nd) in [(0usize, 0usize), (0, 3), (1, 0), (5, 1), (40, 7), (130, 20)] {
            let fp: Vec<C::Point> = (0..nf).map(|_| C::Point::random(&mut rng)).collect();
            let dp: Vec<C::Point> = (0..nd).map(|_| C::Point::random(&mut rng)).collect();
            let special = [C::Scalar::ZERO, C::Scalar::ONE, -C::Scalar::ONE];
            let s = |i: usize, rng: &mut ChaCha20Rng| special.get(i).copied().unwrap_or_else(|| C::Scalar::random(rng));
            let fs: Vec<C::Scalar> = (0..nf).map(|i| s(i, &mut rng)).collect();
            let ds: Vec<C::Scalar> = (0..nd).map(|i| s(i, &mut rng)).collect();
            let table = C::table(&fp);
            let want = C::msm_vt(&fs, &fp) + C::msm_vt(&ds, &dp);
            assert_eq!(C::msm_vt_table(&table, &fs, &ds, &dp), want, "{} fixed, {} other", nf, nd);
        }
    }

    #[test]
    fn table_msm_matches_msm_ristretto() {
        table_msm_matches_msm::<Ristretto>();
    }

    #[test]
    fn table_msm_matches_msm_secp256k1() {
        table_msm_matches_msm::<Secp256k1>();
    }
}

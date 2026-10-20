//! The prime-order groups the proofs run over: ristretto255 (the default) and, with the
//! `secp256k1` feature, secp256k1.

use core::fmt::Debug;

mod ristretto;
pub use self::ristretto::Ristretto;

/// The scalar field of a curve, as gadgets and linear combinations see it.
pub trait Field: ff::PrimeField + Copy + Debug + Default + Send + Sync + zeroize::Zeroize + 'static {}

impl<F: ff::PrimeField + Copy + Debug + Default + Send + Sync + zeroize::Zeroize + 'static> Field for F {}

/// A prime-order group for Bulletproofs and Bulletproofs++.
pub trait Curve: Copy + Clone + Debug + Default + PartialEq + Eq + Send + Sync + 'static {
    /// The scalar field (the group order).
    type Scalar: Field;
    /// A group element.
    type Point: group::Group<Scalar = Self::Scalar> + Copy + Debug + Send + Sync + zeroize::Zeroize;
    /// An encoded group element of `POINT_BYTES` bytes.
    type Compressed: Copy + Clone + Debug + PartialEq + Eq + Default + Send + Sync;
    /// The name used in transcripts: `"ristretto255"`, `"secp256k1"`.
    const NAME: &'static str;
    /// Length of an encoded point.
    const POINT_BYTES: usize;

    /// The encoding of `p`.
    fn compress(p: &Self::Point) -> Self::Compressed;
    /// The bytes of an encoding (`POINT_BYTES` of them).
    fn compressed_bytes(c: &Self::Compressed) -> &[u8];
    /// The point `c` encodes; `None` if it encodes no point.
    fn decompress(c: &Self::Compressed) -> Option<Self::Point>;
    /// `bytes` as an encoding (`None` unless `bytes.len() == POINT_BYTES`); no curve check.
    fn compressed_from_slice(bytes: &[u8]) -> Option<Self::Compressed>;
    /// A uniformly random scalar from 64 uniformly random bytes (transcript challenges).
    fn scalar_from_wide(bytes: &[u8; 64]) -> Self::Scalar;
    /// The canonical 32-byte encoding used in proofs.
    fn scalar_to_bytes(s: &Self::Scalar) -> [u8; 32];
    /// The scalar a canonical encoding gives; `None` for a value at least the group order.
    fn scalar_from_canonical(bytes: &[u8; 32]) -> Option<Self::Scalar>;
    /// A point from 64 uniformly random bytes (generator derivation).
    fn point_from_uniform(bytes: &[u8; 64]) -> Self::Point;
    /// `(B, B_blinding)` of `PedersenGens::default()`.
    fn default_pedersen() -> (Self::Point, Self::Point);
    /// `sum s_i P_i` in constant time in the scalars (in parallel with `parallel`).
    fn msm_ct(s: &[Self::Scalar], p: &[Self::Point]) -> Self::Point;
    /// `sum s_i P_i` in variable time: for public scalars only.
    fn msm_vt(s: &[Self::Scalar], p: &[Self::Point]) -> Self::Point;
    /// Invert every entry in place (Montgomery's trick) and return the inverse of their
    /// product; the entries must be non-zero.
    fn batch_invert(s: &mut [Self::Scalar]) -> Self::Scalar;
}

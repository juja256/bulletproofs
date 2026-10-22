//! secp256k1 (k256): constant time with GLV for secrets, SEC1 compressed points (33 bytes),
//! big-endian scalars.

use alloc::vec::Vec;
use core::convert::TryFrom;
use core::fmt;

use k256::elliptic_curve::bigint::U512;
use k256::elliptic_curve::group::Group;
use k256::elliptic_curve::hash2curve::{ExpandMsgXmd, GroupDigest};
use k256::elliptic_curve::ops::{LinearCombinationExt, Reduce};
use k256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use k256::elliptic_curve::PrimeField;
use k256::{AffinePoint, EncodedPoint, FieldBytes, ProjectivePoint, Scalar, WideBytes};
use serde::de::{Error as _, SeqAccess, Visitor};
use serde::ser::SerializeTuple;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::{Curve, Field, PointEncoding};

/// secp256k1 (k256).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Secp256k1;

/// A point as SEC1 compressed bytes (`0x02`/`0x03` || x, 33 bytes); the identity is 33 zero
/// bytes (see [`PointEncoding`]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Secp256k1Compressed(pub [u8; 33]);

impl Default for Secp256k1Compressed {
    fn default() -> Self {
        Secp256k1Compressed([0; 33])
    }
}

impl fmt::Debug for Secp256k1Compressed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Secp256k1Compressed(")?;
        self.0.iter().try_for_each(|b| write!(f, "{:02x}", b))?;
        write!(f, ")")
    }
}

impl PointEncoding for Secp256k1Compressed {
    fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    fn from_slice(bytes: &[u8]) -> Option<Self> {
        <[u8; 33]>::try_from(bytes).ok().map(Secp256k1Compressed)
    }

    fn is_identity(&self) -> bool {
        self.0 == [0; 33]
    }
}

/// A 33-tuple of bytes, as dalek serializes its 32-byte encodings.
impl Serialize for Secp256k1Compressed {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut t = serializer.serialize_tuple(33)?;
        for b in &self.0 {
            t.serialize_element(b)?;
        }
        t.end()
    }
}

impl<'de> Deserialize<'de> for Secp256k1Compressed {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = Secp256k1Compressed;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("33 bytes")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Secp256k1Compressed, A::Error> {
                let mut out = [0u8; 33];
                for (i, b) in out.iter_mut().enumerate() {
                    *b = seq.next_element()?.ok_or_else(|| A::Error::invalid_length(i, &self))?;
                }
                Ok(Secp256k1Compressed(out))
            }
        }
        deserializer.deserialize_tuple(33, V)
    }
}

impl Field for Scalar {
    /// A big-endian 512-bit integer reduced modulo the group order.
    fn from_wide(bytes: &[u8; 64]) -> Scalar {
        <Scalar as Reduce<U512>>::reduce_bytes(WideBytes::from_slice(bytes))
    }

    /// Big-endian.
    fn to_bytes32(&self) -> [u8; 32] {
        self.to_repr().into()
    }

    fn from_bytes32(bytes: &[u8; 32]) -> Option<Scalar> {
        Scalar::from_repr(FieldBytes::from(*bytes)).into()
    }
}

/// H of secp256k1-zkp (`secp256k1_generator_h`, `modules/generator/main_impl.h`): x || y.
const H_XY: [u8; 64] = [
    0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54, 0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a, 0x5e, //
    0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5, 0x47, 0xbf, 0xee, 0x9a, 0xce, 0x80, 0x3a, 0xc0, //
    0x31, 0xd3, 0xc6, 0x86, 0x39, 0x73, 0x92, 0x6e, 0x04, 0x9e, 0x63, 0x7c, 0xb1, 0xb5, 0xf4, 0x0a, //
    0x36, 0xda, 0xc2, 0x8a, 0xf1, 0x76, 0x69, 0x68, 0xc3, 0x0c, 0x23, 0x13, 0xf3, 0xa3, 0x89, 0x04,
];

/// Domain separation of [`Secp256k1::point_from_uniform`] (RFC 9380 hash to curve).
const GENS_DST: &[u8] = b"bulletproofs-secp256k1-gens";

/// Terms per call of k256's constant-time multiscalar multiplication (its tables grow with the
/// number of terms).
const CT_CHUNK: usize = 1 << 10;

fn lincomb(s: &[Scalar], p: &[ProjectivePoint]) -> ProjectivePoint {
    let pairs: Vec<(ProjectivePoint, Scalar)> = p.iter().copied().zip(s.iter().copied()).collect();
    ProjectivePoint::lincomb_ext(&pairs[..])
}

impl Curve for Secp256k1 {
    type Scalar = Scalar;
    type Point = ProjectivePoint;
    type Compressed = Secp256k1Compressed;
    const NAME: &'static str = "secp256k1";
    const POINT_BYTES: usize = 33;

    fn compress(p: &ProjectivePoint) -> Secp256k1Compressed {
        let mut out = [0u8; 33];
        if !bool::from(p.is_identity()) {
            out.copy_from_slice(p.to_affine().to_encoded_point(true).as_bytes());
        }
        Secp256k1Compressed(out)
    }

    fn decompress(c: &Secp256k1Compressed) -> Option<ProjectivePoint> {
        if c.is_identity() {
            return Some(ProjectivePoint::IDENTITY);
        }
        if c.0[0] != 0x02 && c.0[0] != 0x03 {
            return None;
        }
        let ep = EncodedPoint::from_bytes(&c.0[..]).ok()?;
        Option::<AffinePoint>::from(AffinePoint::from_encoded_point(&ep)).map(ProjectivePoint::from)
    }

    fn point_from_uniform(bytes: &[u8; 64]) -> ProjectivePoint {
        k256::Secp256k1::hash_from_bytes::<ExpandMsgXmd<sha2::Sha256>>(&[bytes], &[GENS_DST])
            .expect("a fixed domain separator and message length never fail")
    }

    fn default_pedersen() -> (ProjectivePoint, ProjectivePoint) {
        let h = EncodedPoint::from_untagged_bytes(k256::elliptic_curve::generic_array::GenericArray::from_slice(&H_XY));
        let h = Option::<AffinePoint>::from(AffinePoint::from_encoded_point(&h)).expect("H is on the curve");
        (ProjectivePoint::from(h), ProjectivePoint::GENERATOR)
    }

    /// k256's constant-time Straus with GLV (`lincomb_ext`), by chunks (in parallel with
    /// `parallel`).
    fn msm_ct(s: &[Scalar], p: &[ProjectivePoint]) -> ProjectivePoint {
        assert_eq!(s.len(), p.len());
        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            s.par_chunks(CT_CHUNK)
                .zip(p.par_chunks(CT_CHUNK))
                .map(|(s, p)| lincomb(s, p))
                .reduce(ProjectivePoint::identity, |a, b| a + b)
        }
        #[cfg(not(feature = "parallel"))]
        s.chunks(CT_CHUNK).zip(p.chunks(CT_CHUNK)).map(|(s, p)| lincomb(s, p)).fold(ProjectivePoint::IDENTITY, |a, b| a + b)
    }

    /// Variable time: for public scalars only.
    fn msm_vt(s: &[Scalar], p: &[ProjectivePoint]) -> ProjectivePoint {
        super::pippenger::msm(s, p)
    }
}

// A scalar on the left of a variable or a linear combination (the generic impls have the
// variable or the linear combination on the left).
mod r1cs_ops {
    use core::ops::{Add, Mul, Sub};
    use k256::Scalar;

    use crate::r1cs::{LinearCombination, Variable};

    impl Add<Variable> for Scalar {
        type Output = LinearCombination<Scalar>;

        fn add(self, other: Variable) -> Self::Output {
            LinearCombination::from(self) + other
        }
    }

    impl Sub<Variable> for Scalar {
        type Output = LinearCombination<Scalar>;

        fn sub(self, other: Variable) -> Self::Output {
            LinearCombination::from(self) - other
        }
    }

    impl Mul<Variable> for Scalar {
        type Output = LinearCombination<Scalar>;

        fn mul(self, other: Variable) -> Self::Output {
            other * self
        }
    }

    impl Mul<LinearCombination<Scalar>> for Scalar {
        type Output = LinearCombination<Scalar>;

        fn mul(self, other: LinearCombination<Scalar>) -> Self::Output {
            other * self
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::{Curve, Field, PointEncoding};
    use k256::elliptic_curve::group::Group;
    use k256::elliptic_curve::Field as _;
    use k256::{ProjectivePoint, Scalar};
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    const N: &str = "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141";
    const P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";

    fn arr32(h: &str) -> [u8; 32] {
        let mut b = [0u8; 32];
        b.copy_from_slice(&hex::decode(h).unwrap());
        b
    }

    fn enc(prefix: u8, x: &str) -> Secp256k1Compressed {
        let mut b = vec![prefix];
        b.extend(hex::decode(x).unwrap());
        Secp256k1Compressed::from_slice(&b).unwrap()
    }

    #[test]
    fn multiscalar_multiplication() {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        for n in [0usize, 1, 2, 70, 1500] {
            let s: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let p: Vec<ProjectivePoint> = (0..n).map(|_| ProjectivePoint::random(&mut rng)).collect();
            let naive: ProjectivePoint = s.iter().zip(&p).map(|(s, p)| p * s).sum();
            assert_eq!(Secp256k1::msm_ct(&s, &p), naive, "{}", n);
            assert_eq!(Secp256k1::msm_vt(&s, &p), naive, "{}", n);
        }
        // identities computed by arithmetic among the inputs
        let q = ProjectivePoint::random(&mut rng);
        let s: Vec<Scalar> = (0..40).map(|_| Scalar::random(&mut rng)).collect();
        let mut p: Vec<ProjectivePoint> = (0..40).map(|_| ProjectivePoint::random(&mut rng)).collect();
        p[0] = q - q;
        p[1] = q * Scalar::ZERO;
        let naive: ProjectivePoint = s.iter().zip(&p).map(|(s, p)| p * s).sum();
        assert_eq!(Secp256k1::msm_ct(&s, &p), naive);
        assert_eq!(Secp256k1::msm_vt(&s, &p), naive);
        assert_eq!(Secp256k1::compress(&(q - q)), Secp256k1Compressed::default());
    }

    #[test]
    fn point_encoding() {
        // SEC1 compressed G
        let g = Secp256k1::compress(&ProjectivePoint::GENERATOR);
        assert_eq!(hex::encode(g.as_bytes()), "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
        assert_eq!(Secp256k1::decompress(&g), Some(ProjectivePoint::GENERATOR));
        let minus_g = Secp256k1::compress(&-ProjectivePoint::GENERATOR);
        assert_eq!(minus_g.as_bytes()[0], 0x03);
        assert_eq!(Secp256k1::decompress(&minus_g), Some(-ProjectivePoint::GENERATOR));
        // the identity: 33 zero bytes, both ways
        let id = Secp256k1::compress(&ProjectivePoint::IDENTITY);
        assert_eq!(id, Secp256k1Compressed::default());
        assert!(id.is_identity() && !g.is_identity());
        assert_eq!(Secp256k1::decompress(&id), Some(ProjectivePoint::IDENTITY));
        // malformed: wrong prefix, x >= p, x off the curve, the wrong length
        let gx = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        for prefix in [0x00, 0x01, 0x04, 0x05, 0x06, 0x07, 0x08, 0xff] {
            assert_eq!(Secp256k1::decompress(&enc(prefix, gx)), None, "prefix {:#x}", prefix);
        }
        assert_eq!(Secp256k1::decompress(&enc(0x02, P)), None, "x = p");
        assert_eq!(Secp256k1::decompress(&enc(0x02, &"ff".repeat(32))), None, "x > p");
        // x = 5: 5^3 + 7 = 132 is no square mod p
        assert_eq!(Secp256k1::decompress(&enc(0x02, &format!("{:064x}", 5))), None, "off the curve");
        let mut zero_but_prefix = [0u8; 33];
        zero_but_prefix[0] = 2;
        assert_eq!(Secp256k1::decompress(&Secp256k1Compressed(zero_but_prefix)), None);
        assert_eq!(Secp256k1Compressed::from_slice(&[2u8; 32]), None);
        assert_eq!(Secp256k1Compressed::from_slice(&[2u8; 34]), None);
        assert_eq!(Secp256k1::POINT_BYTES, 33);
        assert_eq!(Secp256k1::NAME, "secp256k1");
    }

    #[test]
    fn scalar_encoding() {
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let s = Scalar::random(&mut rng);
        assert_eq!(Scalar::from_bytes32(&s.to_bytes32()), Some(s));
        // big-endian
        assert_eq!(Scalar::ONE.to_bytes32(), arr32(&format!("{:064x}", 1)));
        // the group order and above are not canonical
        assert_eq!(Scalar::from_bytes32(&arr32(N)), None);
        assert_eq!(Scalar::from_bytes32(&[0xff; 32]), None);
        assert_eq!(Scalar::from_bytes32(&[0; 32]), Some(Scalar::ZERO));
        // a wide reduction of a big-endian 512-bit integer
        let mut wide = [0u8; 64];
        wide[63] = 1;
        assert_eq!(Scalar::from_wide(&wide), Scalar::ONE);
        wide[32..].copy_from_slice(&arr32(N));
        assert_eq!(Scalar::from_wide(&wide), Scalar::ZERO);
        let mut two256 = [0u8; 64];
        two256[31] = 1; // 2^256 = 2^256 - n mod n
        let r = arr32("000000000000000000000000000000014551231950b75fc4402da1732fc9bebf");
        assert_eq!(Scalar::from_wide(&two256), Scalar::from_bytes32(&r).unwrap());
        // the default batch inversion (Montgomery's trick, partial products wiped)
        let xs: Vec<Scalar> = (0..9).map(|_| Scalar::random(&mut rng)).collect();
        let mut inv = xs.clone();
        let all = <Scalar as Field>::batch_invert(&mut inv);
        assert!(inv.iter().zip(&xs).all(|(i, x)| *i * x == Scalar::ONE));
        assert_eq!(all, xs.iter().product::<Scalar>().invert().unwrap());
    }

    #[test]
    fn generators() {
        // B = H of secp256k1-zkp, B_blinding = G
        let (b, bb) = Secp256k1::default_pedersen();
        assert_eq!(
            hex::encode(Secp256k1::compress(&b).as_bytes()),
            "0250929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"
        );
        assert_eq!(bb, ProjectivePoint::GENERATOR);
        let pc = crate::PedersenGens::<Secp256k1>::default();
        assert_eq!((pc.B, pc.B_blinding), (b, bb));
        // hash to curve: deterministic, distinct, never the identity
        let (u1, u2) = (Secp256k1::point_from_uniform(&[1; 64]), Secp256k1::point_from_uniform(&[2; 64]));
        assert_eq!(u1, Secp256k1::point_from_uniform(&[1; 64]));
        assert!(u1 != u2 && !bool::from(u1.is_identity()));
        let bp = crate::BulletproofGens::<Secp256k1>::new(4, 2);
        let g: Vec<ProjectivePoint> = bp.share(1).G(4).cloned().collect();
        assert!(g.windows(2).all(|w| w[0] != w[1]));
    }

    /// A scalar on the left of a variable or a linear combination, as with ristretto255.
    #[test]
    fn scalar_operators_with_variables() {
        use crate::r1cs::{LinearCombination, Variable};
        let (two, v) = (Scalar::from(2u64), Variable::Committed(0));
        let lc = |t: &[(Variable, Scalar)]| t.iter().collect::<LinearCombination<Scalar>>();
        assert_eq!(two + v, lc(&[(Variable::One(), two), (v, Scalar::ONE)]));
        assert_eq!(two - v, lc(&[(Variable::One(), two), (v, -Scalar::ONE)]));
        assert_eq!(two * v, v * two);
        assert_eq!(two * LinearCombination::from(v), v * two);
    }

    #[test]
    fn serde_round_trip() {
        let g = Secp256k1::compress(&ProjectivePoint::GENERATOR);
        let bytes = bincode::serialize(&g).unwrap();
        assert_eq!(bytes, g.as_bytes(), "a 33-tuple, as dalek's 32-tuple");
        assert_eq!(bincode::deserialize::<Secp256k1Compressed>(&bytes).unwrap(), g);
        assert!(bincode::deserialize::<Secp256k1Compressed>(&bytes[..32]).is_err());
    }
}

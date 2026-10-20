//! Compatibility with Elements / secp256k1-zkp: asset generators (`generator_generate`),
//! the value generator H, and the 33-byte encodings of generators and Pedersen commitments.

use k256::elliptic_curve::sec1::FromEncodedPoint;
use k256::elliptic_curve::subtle::{Choice, ConditionallySelectable};
use k256::{AffinePoint, EncodedPoint, FieldBytes, FieldElement, ProjectivePoint, Scalar};
use sha2::{Digest, Sha256};

use crate::curve::{Curve, Secp256k1};

/// `-c` with `c = sqrt(-3)` (`main_impl.h`, `negc`).
const NEGC: [u8; 32] = [
    0xf5, 0xd2, 0xd4, 0x56, 0xca, 0xf8, 0x0e, 0x20, 0xdc, 0xc8, 0x8f, 0x3d, 0x58, 0x68, 0x69, 0xd3, //
    0x39, 0xe0, 0x92, 0xea, 0x25, 0xeb, 0x13, 0x2b, 0x82, 0x72, 0xd8, 0x50, 0xe3, 0x2a, 0x03, 0xdd,
];
/// `d = (c - 1) / 2` (`main_impl.h`, `d`).
const D: [u8; 32] = [
    0x85, 0x16, 0x95, 0xd4, 0x9a, 0x83, 0xf8, 0xef, 0x91, 0x9b, 0xb8, 0x61, 0x53, 0xcb, 0xcb, 0x16, //
    0x63, 0x0f, 0xb6, 0x8a, 0xed, 0x0a, 0x76, 0x6a, 0x3e, 0xc6, 0x93, 0xd6, 0x8e, 0x6a, 0xfa, 0x40,
];

fn fe(bytes: &[u8; 32]) -> FieldElement {
    FieldElement::from_bytes(&FieldBytes::from(*bytes)).unwrap()
}

/// 32 big-endian bytes modulo p, as `secp256k1_fe_set_b32_limit` leaves them (a value at least
/// p, probability 2^-128 for a hash, is reduced; secp256k1-zkp then reports failure but still
/// returns the point).
fn fe_mod_p(bytes: &[u8; 32]) -> FieldElement {
    // v - p = v + (2^32 + 977) - 2^256 for p <= v < 2^256
    let mut reduced = *bytes;
    let mut carry = 0x1000003d1u64;
    for b in reduced.iter_mut().rev() {
        let s = *b as u64 + (carry & 0xff);
        *b = s as u8;
        carry = (carry >> 8) + (s >> 8);
    }
    let direct = FieldElement::from_bytes(&FieldBytes::from(*bytes));
    let low = FieldElement::from_bytes(&FieldBytes::from(reduced)).unwrap_or(FieldElement::ZERO);
    FieldElement::conditional_select(&low, &direct.unwrap_or(FieldElement::ZERO), direct.is_some())
}

/// `(sqrt(a), a is a square)` (the root is meaningful only for a square).
fn sqrt(a: &FieldElement) -> (FieldElement, Choice) {
    let r = a.sqrt();
    (r.unwrap_or(FieldElement::ZERO), r.is_some())
}

/// The Shallue–van de Woestijne map of secp256k1-zkp (`shallue_van_de_woestijne`,
/// `modules/generator/main_impl.h`), step by step; constant time. k256's field elements are
/// lazily reduced: every operand of a negation is brought to magnitude 1 first.
pub(crate) fn svdw(t: &FieldElement) -> AffinePoint {
    let b = FieldElement::from(7u64);
    let wd0 = t.square(); // t^2
    let x1n = fe(&NEGC) * &wd0; // -c t^2
    let x3d = (wd0 + &wd0 + &wd0).normalize_weak().negate(1).normalize_weak(); // -3 t^2
    let wd = (wd0 + &b + &FieldElement::ONE).normalize_weak(); // 1 + b + t^2
    // 1 / (wd x3d), zero for t = 0 (secp256k1_fe_inv returns 0 on 0)
    let jinv = (wd * &x3d).invert().unwrap_or(FieldElement::ZERO);
    let x1 = (fe(&D) + &(x1n * &x3d * &jinv)).normalize_weak();
    let x2 = (x1 + &FieldElement::ONE).normalize_weak().negate(1).normalize_weak();
    let x3 = (wd.square() * &wd * &jinv + &FieldElement::ONE).normalize_weak();
    let f = |x: &FieldElement| (x.square() * x + &b).normalize_weak();
    let (y1, alpha) = sqrt(&f(&x1));
    let (y2, beta) = sqrt(&f(&x2));
    let (y3, _) = sqrt(&f(&x3));
    let (pick2, pick3) = (!alpha & beta, !alpha & !beta);
    let x = FieldElement::conditional_select(&FieldElement::conditional_select(&x1, &x2, pick2), &x3, pick3);
    let y = FieldElement::conditional_select(&FieldElement::conditional_select(&y1, &y2, pick2), &y3, pick3);
    // the sign of y follows the oddness of t
    let y = FieldElement::conditional_select(&y, &y.normalize_weak().negate(1), t.normalize().is_odd());
    // k256 has no public (x, y) constructor: through the uncompressed SEC1 encoding
    let e = EncodedPoint::from_affine_coordinates(&x.normalize().to_bytes(), &y.normalize().to_bytes(), false);
    Option::from(AffinePoint::from_encoded_point(&e)).expect("(x, y) is on the curve by construction")
}

fn hash_to_field(prefix: &[u8; 16], key: &[u8; 32]) -> FieldElement {
    let mut h = Sha256::new();
    h.update(prefix);
    h.update(key);
    fe_mod_p(&h.finalize().into())
}

/// The asset generator of `key` (`secp256k1_generator_generate`): the sum of the map at the
/// field elements SHA256("1st generation: " || key) and SHA256("2nd generation: " || key).
pub fn generator_generate(key: &[u8; 32]) -> ProjectivePoint {
    ProjectivePoint::from(svdw(&hash_to_field(b"1st generation: ", key))) + svdw(&hash_to_field(b"2nd generation: ", key))
}

/// A blinded asset generator (`secp256k1_generator_generate_blinded`):
/// `generator_generate(key) + blind * G`.
pub fn generator_generate_blinded(key: &[u8; 32], blind: &Scalar) -> ProjectivePoint {
    ProjectivePoint::GENERATOR * blind + generator_generate(key)
}

/// The value generator H of secp256k1-zkp (`secp256k1_generator_h`), the `B` of
/// `PedersenGens::<Secp256k1>::for_curve()`.
pub fn h() -> ProjectivePoint {
    Secp256k1::default_pedersen().0
}

#[cfg(test)]
mod tests {
    use super::*;
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    use k256::{FieldBytes, FieldElement, ProjectivePoint, Scalar};
    use serde_json::Value;

    fn vectors() -> Value {
        serde_json::from_str(include_str!("../tests/vectors/elements/generators.json")).unwrap()
    }

    fn xy(p: &ProjectivePoint) -> (String, String) {
        let e = p.to_affine().to_encoded_point(false);
        (hex::encode(e.x().unwrap()), hex::encode(e.y().unwrap()))
    }

    fn hex32(v: &Value) -> [u8; 32] {
        let mut b = [0u8; 32];
        b.copy_from_slice(&hex::decode(v.as_str().unwrap()).unwrap());
        b
    }

    /// The map at t = +-i, i = 0..16 (secp256k1-zkp's SAGE results).
    #[test]
    fn svdw_matches_secp256k1_zkp() {
        for case in vectors()["svdw"].as_array().unwrap() {
            let t = FieldElement::from_bytes(&FieldBytes::from(hex32(&case["t"]))).unwrap();
            let want = (case["x"].as_str().unwrap().to_string(), case["y"].as_str().unwrap().to_string());
            assert_eq!(xy(&ProjectivePoint::from(svdw(&t))), want, "t = {}", case["t"]);
        }
    }

    /// `generator_generate([0; 31] || i)`, i = 1..32, and the blinded variant with blind 0.
    #[test]
    fn generator_generate_matches_secp256k1_zkp() {
        for case in vectors()["generate"].as_array().unwrap() {
            let key = hex32(&case["key"]);
            let want = (case["x"].as_str().unwrap().to_string(), case["y"].as_str().unwrap().to_string());
            assert_eq!(xy(&generator_generate(&key)), want, "key {}", case["key"]);
            assert_eq!(xy(&generator_generate_blinded(&key, &Scalar::ZERO)), want, "key {}", case["key"]);
        }
        // the blinded generator adds blind * G
        let key = [7u8; 32];
        let blind = Scalar::from(5u64);
        assert_eq!(generator_generate_blinded(&key, &blind), generator_generate(&key) + ProjectivePoint::GENERATOR * blind);
        // keys hashing to a field element >= p are not special (secp256k1-zkp also accepts them)
        let _ = generator_generate(&[0xff; 32]);
    }

    /// H is secp256k1-zkp's value generator and the default Pedersen B.
    #[test]
    fn h_is_the_value_generator() {
        use crate::curve::{Curve, Secp256k1};
        assert_eq!(h(), Secp256k1::default_pedersen().0);
    }
}

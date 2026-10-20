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

/// 32 big-endian bytes modulo p. A hash at least p (probability 2^-128) makes secp256k1-zkp
/// report failure; the point it still returns then differs from ours (its unreduced field
/// element has the opposite parity, which flips y in the map), so the generator of such a key
/// is unspecified.
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
///
/// In Elements the key of an asset is its 32-byte asset ID in internal byte order, the reverse
/// of the hex Elements displays (as for transaction IDs): reverse the decoded hex first.
pub fn generator_generate(key: &[u8; 32]) -> ProjectivePoint {
    ProjectivePoint::from(svdw(&hash_to_field(b"1st generation: ", key))) + svdw(&hash_to_field(b"2nd generation: ", key))
}

/// A blinded asset generator (`secp256k1_generator_generate_blinded`):
/// `generator_generate(key) + blind * G`.
pub fn generator_generate_blinded(key: &[u8; 32], blind: &Scalar) -> ProjectivePoint {
    ProjectivePoint::GENERATOR * blind + generator_generate(key)
}

/// secp256k1-zkp's default value generator H (`secp256k1_generator_h`, as in Mimblewimble), the
/// `B` of `PedersenGens::<Secp256k1>::for_curve()`. Liquid commits a value with its asset's
/// generator instead (blinded, or `generator_generate(asset_id)` for an explicit asset), never
/// with H.
pub fn h() -> ProjectivePoint {
    Secp256k1::default_pedersen().0
}

/// Whether `y` is a quadratic residue (constant time).
fn is_square(y: &FieldElement) -> Choice {
    y.sqrt().is_some()
}

/// `prefix ^ is_square(y)` || x for a point other than the identity.
fn serialize(p: &ProjectivePoint, prefix: u8) -> Option<[u8; 33]> {
    use k256::elliptic_curve::group::Group;
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    if bool::from(p.is_identity()) {
        return None;
    }
    let e = p.to_affine().to_encoded_point(false);
    let y = FieldElement::from_bytes(e.y()?).unwrap();
    let mut out = [0u8; 33];
    out[0] = prefix ^ is_square(&y).unwrap_u8();
    out[1..].copy_from_slice(e.x()?);
    Some(out)
}

/// The point with x = `bytes[1..]` whose y is a square for `prefix ^ 1` and no square for
/// `prefix` (p = 3 mod 4: exactly one of +-y is a square); `None` for another prefix or an x
/// of no point.
fn parse(bytes: &[u8; 33], prefix: u8) -> Option<ProjectivePoint> {
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    let want_square = match bytes[0] {
        b if b == prefix => Choice::from(0),
        b if b == prefix ^ 1 => Choice::from(1),
        _ => return None,
    };
    let mut sec1 = *bytes;
    sec1[0] = 0x02;
    let e = EncodedPoint::from_bytes(&sec1[..]).ok()?;
    let p = ProjectivePoint::from(Option::<AffinePoint>::from(AffinePoint::from_encoded_point(&e))?);
    let y = FieldElement::from_bytes(p.to_affine().to_encoded_point(false).y()?).unwrap();
    Some(ProjectivePoint::conditional_select(&-p, &p, !(is_square(&y) ^ want_square)))
}

/// A generator as secp256k1-zkp serializes it (`secp256k1_generator_serialize`): 0x0a if y is
/// a square, 0x0b otherwise, then x; `None` for the identity.
pub fn generator_serialize(p: &ProjectivePoint) -> Option<[u8; 33]> {
    serialize(p, 0x0b)
}

/// `secp256k1_generator_parse`.
pub fn generator_parse(bytes: &[u8; 33]) -> Option<ProjectivePoint> {
    parse(bytes, 0x0b)
}

/// A Pedersen commitment as secp256k1-zkp serializes it
/// (`secp256k1_pedersen_commitment_serialize`): 0x08 if y is a square, 0x09 otherwise, then
/// x; `None` for the identity.
pub fn commitment_serialize(p: &ProjectivePoint) -> Option<[u8; 33]> {
    serialize(p, 0x09)
}

/// `secp256k1_pedersen_commitment_parse`.
pub fn commitment_parse(bytes: &[u8; 33]) -> Option<ProjectivePoint> {
    parse(bytes, 0x09)
}

/// `secp256k1_pedersen_commit`: `value * gen + blinding * G` (constant time).
pub fn commit(value: u64, blinding: &Scalar, gen: &ProjectivePoint) -> ProjectivePoint {
    Secp256k1::msm_ct(&[Scalar::from(value), *blinding], &[*gen, ProjectivePoint::GENERATOR])
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

    }

    /// x(2G), the fixed vectors of test_generator_fixed_vector and
    /// test_pedersen_commitment_fixed_vector.
    const TWO_G_X: &str = "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5";

    fn with_prefix(prefix: u8) -> [u8; 33] {
        let mut b = [prefix; 33];
        b[1..].copy_from_slice(&hex::decode(TWO_G_X).unwrap());
        b
    }

    #[test]
    fn generator_encoding_matches_secp256k1_zkp() {
        let two_g = ProjectivePoint::GENERATOR.double();
        // y(2G) is a square (checked independently), so 2G is 0x0a || x and the vector
        // "two_g" = 0x0b || x(2G) is -2G: the root is chosen by quadratic residuosity (an even
        // y would give 2G for 0x0b: y(2G) is even)
        let p = generator_parse(&with_prefix(0x0b)).unwrap();
        assert_eq!(p, -two_g);
        assert_eq!(generator_serialize(&p), Some(with_prefix(0x0b)));
        assert_eq!(generator_parse(&with_prefix(0x0a)).unwrap(), two_g);
        assert_eq!(generator_serialize(&two_g), Some(with_prefix(0x0a)));
        assert_eq!(generator_serialize(&ProjectivePoint::IDENTITY), None);
        for bad in [0x08, 0x09, 0x02, 0x03, 0x0c, 0x00] {
            assert_eq!(generator_parse(&with_prefix(bad)), None, "prefix {:#x}", bad);
        }
    }

    #[test]
    fn commitment_encoding_matches_secp256k1_zkp() {
        let two_g = ProjectivePoint::GENERATOR.double();
        let p = commitment_parse(&with_prefix(0x09)).unwrap();
        assert_eq!(p, -two_g);
        assert_eq!(commitment_serialize(&p), Some(with_prefix(0x09)));
        assert_eq!(commitment_parse(&with_prefix(0x08)).unwrap(), two_g);
        assert_eq!(commitment_serialize(&two_g), Some(with_prefix(0x08)));
        for bad in [0x0a, 0x0b, 0x0c, 0x02, 0x03, 0x00] {
            assert_eq!(commitment_parse(&with_prefix(bad)), None, "prefix {:#x}", bad);
        }
    }

    /// The prefix follows the quadratic residuosity of y, not its parity: k G for k = 1..12
    /// covers every combination (prefixes computed independently from secp256k1-zkp's rule
    /// `11 ^ is_square(y)`).
    #[test]
    fn prefix_follows_residuosity_not_parity() {
        // (k, generator prefix): 3G, 5G, 7G, 8G have an even non-square y; 6G, 9G, 10G, 12G
        // an odd square y
        let want = [0x0a, 0x0a, 0x0b, 0x0a, 0x0b, 0x0a, 0x0b, 0x0b, 0x0a, 0x0a, 0x0b, 0x0a];
        let mut p = ProjectivePoint::IDENTITY;
        for (k, w) in want.iter().enumerate() {
            p += ProjectivePoint::GENERATOR;
            assert_eq!(generator_serialize(&p).unwrap()[0], *w, "{}G", k + 1);
            assert_eq!(commitment_serialize(&p).unwrap()[0], *w ^ 0x0b ^ 0x09, "{}G", k + 1);
        }
    }

    #[test]
    fn encodings_round_trip_and_reject_malformed() {
        use k256::elliptic_curve::Field as _;
        use rand_chacha::rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(13);
        for _ in 0..100 {
            let p = ProjectivePoint::GENERATOR * Scalar::random(&mut rng);
            assert_eq!(commitment_parse(&commitment_serialize(&p).unwrap()), Some(p));
            assert_eq!(generator_parse(&generator_serialize(&p).unwrap()), Some(p));
        }
        // x >= p, x off the curve (5^3 + 7 is no square)
        let mut b = [0xffu8; 33];
        b[0] = 0x09;
        assert_eq!(commitment_parse(&b), None);
        let mut b = [0u8; 33];
        b[0] = 0x09;
        b[32] = 5;
        assert_eq!(commitment_parse(&b), None);
    }

    /// secp256k1_pedersen_commit: blind * G + value * gen.
    #[test]
    fn commit_is_value_times_generator_plus_blinding() {
        let gen = generator_generate(&[3u8; 32]);
        let r = Scalar::from(11u64);
        assert_eq!(commit(5, &r, &gen), gen * Scalar::from(5u64) + ProjectivePoint::GENERATOR * r);
        assert_eq!(commit(0, &Scalar::ZERO, &gen), ProjectivePoint::IDENTITY);
    }

    /// Hashes at least p are reduced: p, p + 1 and 2^256 - 1.
    #[test]
    fn hashes_reduce_modulo_p() {
        let p = hex32(&Value::from("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"));
        let mut p1 = p;
        p1[31] += 1;
        assert_eq!(fe_mod_p(&p), FieldElement::ZERO);
        assert_eq!(fe_mod_p(&p1), FieldElement::ONE);
        assert_eq!(fe_mod_p(&[0xff; 32]), FieldElement::from(0x1000003d0u64));
        assert_eq!(fe_mod_p(&hex32(&Value::from(format!("{:064x}", 5)))), FieldElement::from(5u64));
    }

    /// H is secp256k1-zkp's value generator and the default Pedersen B.
    #[test]
    fn h_is_the_value_generator() {
        use crate::curve::{Curve, Secp256k1};
        assert_eq!(h(), Secp256k1::default_pedersen().0);
    }
}

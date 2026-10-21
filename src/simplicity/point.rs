//! Points and scalars of the proof in the program: witness decoding, constants, the final
//! multiscalar multiplication.

use k256::elliptic_curve::sec1::ToEncodedPoint;

use crate::simplicity::ir::{Op, Prog, Ty, Val};

/// A point of the proof read from the witness as (parity of y, x).
pub(crate) struct WitPoint {
    /// The parity bit of y.
    pub parity: Val,
    /// x.
    pub x: Val,
    /// The point `(x, y)`, on the curve (`decompress` fails otherwise).
    pub ge: Val,
    /// The first byte of its SEC1 encoding, `0x02 | parity` (for the transcript).
    pub sec1_prefix: Val,
}

/// The type of a witness point: (parity, x).
pub(crate) fn point_ty() -> Ty {
    Ty::prod(Ty::Bit, Ty::word())
}

/// Read the witness point `name` and decompress it.
pub(crate) fn witness_point(p: &mut Prog, name: &str) -> WitPoint {
    let w = p.push(Op::Witness(name.into(), point_ty()));
    let parity = p.push(Op::Fst(w, Ty::Bit));
    let x = p.push(Op::Snd(w, Ty::word()));
    let opt = p.push(Op::Jet("decompress", vec![parity, x], Ty::opt(Ty::ge())));
    let ge = p.push(Op::Unwrap(opt, Ty::ge()));
    let odd = p.push(Op::Const(Ty::Word(8), vec![0x03]));
    let even = p.push(Op::Const(Ty::Word(8), vec![0x02]));
    let sec1_prefix = p.push(Op::Select(parity, odd, even, Ty::Word(8)));
    WitPoint { parity, x, ge, sec1_prefix }
}

/// Read the witness scalar `name`; fails unless it is canonical (below the group order).
pub(crate) fn witness_scalar(p: &mut Prog, name: &str) -> Val {
    let w = p.push(Op::Witness(name.into(), Ty::word()));
    let n = p.push(Op::Jet("scalar_normalize", vec![w], Ty::word()));
    let e = p.push(Op::Jet("eq_256", vec![n, w], Ty::Bit));
    p.push(Op::Assert(e));
    w
}

/// A constant point in Jacobian coordinates `((x, y), 1)` (not the identity).
pub(crate) fn const_gej(p: &mut Prog, pt: &k256::AffinePoint) -> Val {
    let e = pt.to_encoded_point(false);
    let mut b = e.x().expect("not the identity").to_vec();
    b.extend_from_slice(e.y().expect("not the identity"));
    b.extend_from_slice(&one());
    p.push(Op::Const(Ty::gej(), b))
}

fn one() -> [u8; 32] {
    let mut o = [0u8; 32];
    o[31] = 1;
    o
}

/// `(x, y)` as `((x, y), 1)`.
pub(crate) fn ge_to_gej(p: &mut Prog, ge: Val) -> Val {
    let z = p.push(Op::Const(Ty::word(), one().to_vec()));
    p.push(Op::Pair(ge, z, Ty::gej()))
}

/// `Σ k_i · P_i` with `scale` and `gej_add` (no multiscalar jet exists).
pub(crate) fn msm(p: &mut Prog, terms: &[(Val, Val)]) -> Val {
    assert!(!terms.is_empty(), "an empty multiscalar multiplication");
    let mut acc = p.push(Op::Jet("scale", vec![terms[0].0, terms[0].1], Ty::gej()));
    for (k, pt) in &terms[1..] {
        let t = p.push(Op::Jet("scale", vec![*k, *pt], Ty::gej()));
        acc = p.push(Op::Jet("gej_add", vec![acc, t], Ty::gej()));
    }
    acc
}

/// Fail unless `gej` is the point at infinity.
pub(crate) fn assert_infinity(p: &mut Prog, gej: Val) {
    let b = p.push(Op::Jet("gej_is_infinity", vec![gej], Ty::Bit));
    p.push(Op::Assert(b));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::ir::{Op, Prog, Ty};
    use crate::simplicity::run::{bit_value, dummy_env, execute_text_unbudgeted, word_value};
    use k256::elliptic_curve::ff::{Field as _, PrimeField as _};
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    use k256::{AffinePoint, ProjectivePoint, Scalar};
    use rand_chacha::rand_core::SeedableRng;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn xy(p: &ProjectivePoint) -> (bool, Vec<u8>, Vec<u8>) {
        let e = p.to_affine().to_encoded_point(false);
        let y = e.y().unwrap().to_vec();
        (y[31] & 1 == 1, e.x().unwrap().to_vec(), y)
    }

    fn point_value(p: &ProjectivePoint, flip_x: bool) -> ::simplicity::Value {
        let (odd, mut x, _) = xy(p);
        if flip_x {
            x[31] ^= 1;
        }
        ::simplicity::Value::product(bit_value(odd), word_value(&x))
    }

    fn neg_one() -> Vec<u8> {
        (-Scalar::ONE).to_repr().to_vec()
    }

    fn relation(flip: bool) -> bool {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let (a, b) = (Scalar::random(&mut rng), Scalar::random(&mut rng));
        let (pp, qq) = (ProjectivePoint::GENERATOR * a, ProjectivePoint::GENERATOR * b);
        let mut p = Prog::new();
        let wp = witness_point(&mut p, "p0");
        let wq = witness_point(&mut p, "p1");
        let g = const_gej(&mut p, &AffinePoint::GENERATOR);
        let ka = p.push(Op::Const(Ty::word(), a.to_repr().to_vec()));
        let kb = p.push(Op::Const(Ty::word(), b.to_repr().to_vec()));
        let m1 = p.push(Op::Const(Ty::word(), neg_one()));
        let (gp, gq) = (ge_to_gej(&mut p, wp.ge), ge_to_gej(&mut p, wq.ge));
        let acc = msm(&mut p, &[(ka, g), (kb, g), (m1, gp), (m1, gq)]);
        assert_infinity(&mut p, acc);
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("p0"), point_value(&pp, false));
        w.insert(Arc::<str>::from("p1"), point_value(&qq, flip));
        execute_text_unbudgeted(&p.to_text(), &w, &dummy_env()).is_ok()
    }

    #[test]
    fn msm_of_a_relation_is_infinity() {
        assert!(relation(false));
        assert!(!relation(true));
    }

    fn scalar_program(bytes: Vec<u8>) -> bool {
        let mut p = Prog::new();
        let s = witness_scalar(&mut p, "s0");
        let z = p.push(Op::Jet("scalar_is_zero", vec![s], Ty::Bit));
        let nz = p.push(Op::Jet("complement_1", vec![z], Ty::Bit));
        p.push(Op::Assert(nz));
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("s0"), word_value(&bytes));
        execute_text_unbudgeted(&p.to_text(), &w, &dummy_env()).is_ok()
    }

    #[test]
    fn non_canonical_scalar_fails() {
        let n = hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let mut n1 = n.clone();
        n1[31] -= 1;
        assert!(!scalar_program(n));
        assert!(scalar_program(n1));
    }

    #[test]
    fn parity_selects_the_sec1_prefix() {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(4);
        let mut seen = [false; 2];
        while seen != [true, true] {
            let pt = ProjectivePoint::GENERATOR * Scalar::random(&mut rng);
            let (odd, _, _) = xy(&pt);
            seen[odd as usize] = true;
            let run = |expected: u8| {
                let mut p = Prog::new();
                let wp = witness_point(&mut p, "p0");
                let k = p.push(Op::Const(Ty::Word(8), vec![expected]));
                let e = p.push(Op::Jet("eq_8", vec![wp.sec1_prefix, k], Ty::Bit));
                p.push(Op::Assert(e));
                // the decoded point is used too, so that it is checked
                let one = p.push(Op::Const(Ty::word(), Scalar::ONE.to_repr().to_vec()));
                let g = ge_to_gej(&mut p, wp.ge);
                let acc = msm(&mut p, &[(one, g)]);
                let inf = p.push(Op::Jet("gej_is_infinity", vec![acc], Ty::Bit));
                let ninf = p.push(Op::Jet("complement_1", vec![inf], Ty::Bit));
                p.push(Op::Assert(ninf));
                let mut w = HashMap::new();
                w.insert(Arc::<str>::from("p0"), point_value(&pt, false));
                execute_text_unbudgeted(&p.to_text(), &w, &dummy_env()).is_ok()
            };
            let right = if odd { 0x03 } else { 0x02 };
            assert!(run(right));
            assert!(!run(right ^ 1));
        }
    }

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }
}

//! Every proof over every curve: generic helpers called for ristretto255 and, with the
//! `secp256k1` feature, secp256k1.

#![allow(non_snake_case)]

use bulletproofs::curve::Ristretto;
use bulletproofs::{BulletproofGens, PedersenGens};

/// The default curve is Ristretto: the old spelling and the new one agree.
#[test]
fn ristretto_generators_unchanged() {
    let a = PedersenGens::default();
    let b = PedersenGens::<Ristretto>::default();
    assert_eq!((a.B, a.B_blinding), (b.B, b.B_blinding));
    let g = BulletproofGens::new(64, 2);
    let h = BulletproofGens::<Ristretto>::new(64, 2);
    for j in 0..2 {
        assert!(g.share(j).G(64).zip(h.share(j).G(64)).all(|(x, y)| x == y));
    }
}

mod bp {
    use bulletproofs::curve::ff::Field as _;
    use bulletproofs::curve::{Curve, Ristretto};
    use bulletproofs::{BulletproofGens, LinearProof, PedersenGens, RangeProof};
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// Single and aggregated range proofs (the latter through the MPC dealer and parties),
    /// with the encoding round trip and a wrong transcript.
    pub fn range_roundtrip<C: Curve>() {
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(64, 4);
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let blind = C::Scalar::random(&mut rng);
        let (proof, com) =
            RangeProof::<C>::prove_single_with_rng(&bp, &pc, &mut Transcript::new(b"t"), 1_234_567, &blind, 32, &mut rng).unwrap();
        let parsed = RangeProof::<C>::from_bytes(&proof.to_bytes()).unwrap();
        parsed.verify_single(&bp, &pc, &mut Transcript::new(b"t"), &com, 32).unwrap();
        assert!(parsed.verify_single(&bp, &pc, &mut Transcript::new(b"x"), &com, 32).is_err());
        let blinds: Vec<C::Scalar> = (0..4).map(|_| C::Scalar::random(&mut rng)).collect();
        let (p, coms) =
            RangeProof::<C>::prove_multiple_with_rng(&bp, &pc, &mut Transcript::new(b"m"), &[1, 2, 3, 4], &blinds, 16, &mut rng).unwrap();
        p.verify_multiple(&bp, &pc, &mut Transcript::new(b"m"), &coms, 16).unwrap();
        assert!(p.verify_multiple(&bp, &pc, &mut Transcript::new(b"m"), &coms, 8).is_err());
    }

    /// `<a, b>` with a committed `a`.
    pub fn linear_roundtrip<C: Curve>() {
        let mut rng = ChaCha20Rng::seed_from_u64(6);
        let n = 8;
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(n, 1);
        let G: Vec<C::Point> = bp.share(0).G(n).cloned().collect();
        let a: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let b: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let c: C::Scalar = a.iter().zip(&b).map(|(x, y)| *x * y).sum();
        let r = C::Scalar::random(&mut rng);
        // C = <a, G> + r B + <a, b> F with F = pc.B, B = pc.B_blinding
        let mut s = a.clone();
        s.push(r);
        s.push(c);
        let mut pts = G.clone();
        pts.push(pc.B_blinding);
        pts.push(pc.B);
        let com = C::compress(&C::msm_vt(&s, &pts));
        let proof = LinearProof::<C>::create(&mut Transcript::new(b"l"), &mut rng, &com, r, a, b.clone(), G.clone(), &pc.B, &pc.B_blinding).unwrap();
        let parsed = LinearProof::<C>::from_bytes(&proof.to_bytes()).unwrap();
        parsed.verify(&mut Transcript::new(b"l"), &com, &G, &pc.B, &pc.B_blinding, b.clone()).unwrap();
        assert!(parsed.verify(&mut Transcript::new(b"x"), &com, &G, &pc.B, &pc.B_blinding, b).is_err());
    }

    #[test]
    fn range_proofs_ristretto() {
        range_roundtrip::<Ristretto>();
    }

    #[test]
    fn linear_proofs_ristretto() {
        linear_roundtrip::<Ristretto>();
    }
}

#[cfg(feature = "bppp")]
mod bppp {
    use bulletproofs::bppp::{BatchVerifier, RangeProof, RangeStatement};
    use bulletproofs::curve::ff::Field as _;
    use bulletproofs::curve::{Curve, Ristretto};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// A BP++ range proof for two values: prove, encoding round trip, verify, batch verify,
    /// a wrong transcript and an out-of-range value.
    pub fn bppp_range_roundtrip<C: Curve>() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let st = RangeStatement::new(16, vec![(0, 1 << 32), (10, 1000)]).unwrap();
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(st.generators_capacity(), 1);
        let blinds: Vec<C::Scalar> = (0..2).map(|_| C::Scalar::random(&mut rng)).collect();
        let (proof, V) = RangeProof::<C>::prove(&st, &pc, &bp, &[123_456, 999], &blinds, &mut Transcript::new(b"r"), &mut rng).unwrap();
        let parsed = RangeProof::<C>::from_bytes(&proof.to_bytes(), &st).unwrap();
        assert_eq!(parsed, proof);
        parsed.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"r")).unwrap();
        assert!(parsed.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"x")).is_err());
        let mut batch = BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(8));
        batch.add_range(&parsed, &st, &V, &mut Transcript::new(b"r")).unwrap();
        batch.verify().unwrap();
        assert!(RangeProof::<C>::prove(&st, &pc, &bp, &[123_456, 1000], &blinds, &mut Transcript::new(b"r"), &mut rng).is_err());
    }

    #[test]
    fn bppp_range_proofs_ristretto() {
        bppp_range_roundtrip::<Ristretto>();
    }
}

/// The identity's encoding (the `Curve` contract): `compress` is total, the identity encodes as
/// `Compressed::default()`, which decodes back to it and is the only encoding `is_identity`
/// accepts. One-phase R1CS proofs send the identity for the second-phase commitments.
#[cfg(feature = "yoloproofs")]
mod identity {
    use bulletproofs::curve::group::Group;
    use bulletproofs::curve::{Curve, PointEncoding, Ristretto};
    use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    pub fn identity_contract<C: Curve>() {
        let id = C::compress(&C::Point::identity());
        assert_eq!(id, C::Compressed::default());
        assert!(id.is_identity());
        assert_eq!(C::decompress(&id), Some(C::Point::identity()));
        let (b, _) = C::default_pedersen();
        assert!(!C::compress(&b).is_identity());
    }

    /// `x * y = 12` without randomized constraints: a one-phase proof, round trip and verify.
    pub fn one_phase_r1cs<C: Curve>() {
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(8, 1);
        let mut t = Transcript::new(b"one phase");
        let mut prover = Prover::new(&pc, &mut t);
        let (cx, x) = prover.commit(C::Scalar::from(3u64), C::Scalar::from(5u64));
        let (cy, y) = prover.commit(C::Scalar::from(4u64), C::Scalar::from(6u64));
        let (_, _, o) = prover.multiply(x.into(), y.into());
        prover.constrain(o - C::Scalar::from(12u64));
        let proof = R1CSProof::<C>::from_bytes(&prover.prove(&bp).unwrap().to_bytes()).unwrap();
        let mut t = Transcript::new(b"one phase");
        let mut verifier = Verifier::<_, C>::for_curve(&mut t);
        let (x, y) = (verifier.commit(cx), verifier.commit(cy));
        let (_, _, o) = verifier.multiply(x.into(), y.into());
        verifier.constrain(o - C::Scalar::from(12u64));
        verifier.verify(&proof, &pc, &bp).unwrap();
    }

    #[test]
    fn ristretto_identity_contract() {
        identity_contract::<Ristretto>();
        one_phase_r1cs::<Ristretto>();
    }
}

/// Upstream ristretto255 gadgets with integer constants of every width still compile.
#[cfg(feature = "yoloproofs")]
mod upstream_integers {
    use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable};

    #[allow(dead_code)]
    fn gadget<CS: ConstraintSystem>(cs: &mut CS, a: Variable, b: Variable) {
        cs.constrain(a * 2u32 + 1u8 - b);
        cs.constrain(a + 1u16 - (b - 1u128));
        cs.constrain(LinearCombination::from(3u32) - a * 4u8);
        cs.constrain(LinearCombination::from(a) * 2u16 - b * 7u128);
    }

    #[test]
    fn upstream_integer_constants_compile() {}
}

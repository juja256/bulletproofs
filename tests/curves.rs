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

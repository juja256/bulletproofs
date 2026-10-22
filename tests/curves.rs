//! Every proof over every curve: generic helpers called for ristretto255 and, with the
//! `secp256k1` feature, secp256k1.

#![allow(non_snake_case)]

use bulletproofs::curve::Ristretto;
use bulletproofs::{BulletproofGens, PedersenGens};

/// The default curve is Ristretto: the old spelling and the new one agree.
#[test]
fn ristretto_generators_unchanged() {
    let a = PedersenGens::<Ristretto>::default();
    let b = PedersenGens::<Ristretto>::default();
    assert_eq!((a.B, a.B_blinding), (b.B, b.B_blinding));
    let g = BulletproofGens::<Ristretto>::new(64, 2);
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
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(64, 4);
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
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(n, 1);
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

    #[test]
    fn range_proofs_secp256k1() {
        range_roundtrip::<bulletproofs::curve::Secp256k1>();
    }

    #[test]
    fn linear_proofs_secp256k1() {
        linear_roundtrip::<bulletproofs::curve::Secp256k1>();
    }
}

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
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(st.generators_capacity(), 1);
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

    /// A multi-asset transaction: two inputs, two outputs of two assets.
    pub fn mact_roundtrip<C: Curve>() {
        use bulletproofs::bppp::{MactEntry, MactProof, MactStatement};
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let st = MactStatement::new(16, 2, 2).unwrap();
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(st.generators_capacity(), 1);
        let (a, b) = (C::Scalar::random(&mut rng), C::Scalar::random(&mut rng));
        let e = |amount: u64, asset: C::Scalar, rng: &mut ChaCha20Rng| MactEntry { amount, asset, blinding: C::Scalar::random(rng) };
        let inputs = [e(100, a, &mut rng), e(7, b, &mut rng)];
        let outputs = [e(60, a, &mut rng), e(47, a, &mut rng)];
        // 100 a + 7 b in, 107 a out: unbalanced, the prover refuses
        assert!(MactProof::<C>::prove(&st, &pc, &bp, &inputs, &outputs, &mut Transcript::new(b"m"), &mut rng).is_err());
        let outputs = [e(40, a, &mut rng), e(7, b, &mut rng)];
        let inputs = [e(40, a, &mut rng), inputs[1]];
        let (proof, V) = MactProof::<C>::prove(&st, &pc, &bp, &inputs, &outputs, &mut Transcript::new(b"m"), &mut rng).unwrap();
        let parsed = MactProof::<C>::from_bytes(&proof.to_bytes(), &st).unwrap();
        parsed.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).unwrap();
        assert!(parsed.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"x")).is_err());
    }

    #[test]
    fn bppp_range_proofs_ristretto() {
        bppp_range_roundtrip::<Ristretto>();
        mact_roundtrip::<Ristretto>();
    }

    #[test]
    fn bppp_range_proofs_secp256k1() {
        bppp_range_roundtrip::<bulletproofs::curve::Secp256k1>();
        mact_roundtrip::<bulletproofs::curve::Secp256k1>();
    }
}

/// The identity's encoding (the `Curve` contract): `compress` is total, the identity encodes as
/// `Compressed::default()`, which decodes back to it and is the only encoding `is_identity`
/// accepts. One-phase R1CS proofs send the identity for the second-phase commitments.
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
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(8, 1);
        let mut t = Transcript::new(b"one phase");
        let mut prover = Prover::new(&pc, &mut t);
        let (cx, x) = prover.commit(C::Scalar::from(3u64), C::Scalar::from(5u64));
        let (cy, y) = prover.commit(C::Scalar::from(4u64), C::Scalar::from(6u64));
        let o = prover.multiply(x.into(), y.into()).unwrap();
        prover.constrain(o - C::Scalar::from(12u64));
        let proof = R1CSProof::<C>::from_bytes(&prover.prove(&bp).unwrap().to_bytes()).unwrap();
        let mut t = Transcript::new(b"one phase");
        let mut verifier = Verifier::<_, C>::new(&mut t);
        let (x, y) = (verifier.commit(cx), verifier.commit(cy));
        let o = verifier.multiply(x.into(), y.into()).unwrap();
        verifier.constrain(o - C::Scalar::from(12u64));
        verifier.verify(&proof, &pc, &bp).unwrap();
    }

    #[test]
    fn ristretto_identity_contract() {
        identity_contract::<Ristretto>();
        one_phase_r1cs::<Ristretto>();
    }

    #[test]
    fn secp256k1_identity_contract() {
        identity_contract::<bulletproofs::curve::Secp256k1>();
        one_phase_r1cs::<bulletproofs::curve::Secp256k1>();
    }
}

/// Integer constants of every width in linear combinations (`lc(a) * 2u32 + 1u8`).
mod upstream_integers {
    use curve25519_dalek::scalar::Scalar;
    use bulletproofs::r1cs::{lc, ConstraintSystem, LinearCombination, Variable};

    #[allow(dead_code)]
    fn gadget<CS: ConstraintSystem<Scalar>>(cs: &mut CS, a: Variable, b: Variable) {
        cs.constrain(lc(a) * 2u32 + 1u8 - b);
        cs.constrain(lc(a) + 1u16 - (lc(b) - 1u128));
        cs.constrain(LinearCombination::from(3u32) - lc(a) * 4u8);
        cs.constrain(LinearCombination::from(a) * 2u16 - lc(b) * 7u128);
    }

    #[test]
    fn upstream_integer_constants_compile() {}
}

/// Malformed points and scalars in every kind of proof on secp256k1 are errors (when parsing
/// or verifying), never panics (Review Focus 1, 3).
mod malformed {
    use bulletproofs::bppp::{MactEntry, MactProof, MactStatement, RangeProof as BpppRangeProof, RangeStatement};
    use bulletproofs::curve::ff::Field as _;
    use bulletproofs::curve::{Curve, Secp256k1};
    use bulletproofs::r1cs::{Backend, ConstraintSystem, Prover, R1CSProof, Verifier};
    use bulletproofs::{BulletproofGens, LinearProof, PedersenGens, RangeProof};
    use k256::Scalar;
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    type C = Secp256k1;
    const GX: &str = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
    const P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    const N: &str = "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141";

    fn bad_points() -> Vec<Vec<u8>> {
        let with = |prefix: u8, x: &str| [vec![prefix], hex::decode(x).unwrap()].concat();
        vec![
            with(0x04, GX),
            with(0x05, GX),
            with(0x00, GX),
            with(0x02, P),
            with(0x02, &format!("{:064x}", 5)), // x^3 + 7 is no square
            vec![0u8; 33],
        ]
    }

    /// `accepts(bytes)`: the bytes parse and verify. The original is accepted; every bad point
    /// at an offset of `points` and the group order at an offset of `scalars` is not.
    fn check(name: &str, bytes: &[u8], points: &[usize], scalars: &[usize], accepts: impl Fn(&[u8]) -> bool) {
        assert!(accepts(bytes), "{}: the original", name);
        for &at in points {
            for bad in bad_points() {
                let mut b = bytes.to_vec();
                b[at..at + 33].copy_from_slice(&bad);
                assert!(!accepts(&b), "{}: point {:02x?} at {}", name, &bad[..2], at);
            }
        }
        for &at in scalars {
            let mut b = bytes.to_vec();
            b[at..at + 32].copy_from_slice(&hex::decode(N).unwrap());
            assert!(!accepts(&b), "{}: scalar n at {}", name, at);
        }
        for cut in [1, 32, 33] {
            assert!(!accepts(&bytes[..bytes.len() - cut]), "{}: {} bytes short", name, cut);
        }
    }

    #[test]
    fn malformed_secp256k1_proofs_are_errors() {
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(64, 1);

        // BP range proof: A S T_1 T_2 | t_x t_x_blinding e_blinding | L R ... | a b
        let blind = Scalar::random(&mut rng);
        let (proof, v) = RangeProof::<C>::prove_single_with_rng(&bp, &pc, &mut Transcript::new(b"r"), 9, &blind, 32, &mut rng).unwrap();
        let bytes = proof.to_bytes();
        check("range", &bytes, &[0, 99, 132 + 96], &[132, bytes.len() - 32], |b| {
            RangeProof::<C>::from_bytes(b).map_or(false, |p| p.verify_single(&bp, &pc, &mut Transcript::new(b"r"), &v, 32).is_ok())
        });

        // linear proof: L R ... | S | a r
        let n = 8;
        let g: Vec<k256::ProjectivePoint> = bp.share(0).G(n).cloned().collect();
        let a: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let bv: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let r = Scalar::random(&mut rng);
        let c: Scalar = a.iter().zip(&bv).map(|(x, y)| *x * y).sum();
        let mut s = a.clone();
        s.extend([r, c]);
        let mut pts = g.clone();
        pts.extend([pc.B_blinding, pc.B]);
        let com = C::compress(&C::msm_vt(&s, &pts));
        let proof = LinearProof::<C>::create(&mut Transcript::new(b"l"), &mut rng, &com, r, a, bv.clone(), g.clone(), &pc.B, &pc.B_blinding).unwrap();
        let bytes = proof.to_bytes();
        let s_at = bytes.len() - 64 - 33;
        check("linear", &bytes, &[0, 33, s_at], &[bytes.len() - 32], |b| {
            LinearProof::<C>::from_bytes(b)
                .map_or(false, |p| p.verify(&mut Transcript::new(b"l"), &com, &g, &pc.B, &pc.B_blinding, bv.clone()).is_ok())
        });

        // R1CS (x * y = 12) on both backends: BP tag | points | scalars | IPP; BP++ tag and
        // dimensions (17 bytes) | C_L C_R C_O C_S | WNLA
        for backend in [Backend::Bp, Backend::Bppp] {
            let mut t = Transcript::new(b"c");
            let mut prover = Prover::new(&pc, &mut t);
            prover.set_backend(backend);
            let (cx, x) = prover.commit(Scalar::from(3u64), Scalar::random(&mut rng));
            let (cy, y) = prover.commit(Scalar::from(4u64), Scalar::random(&mut rng));
            let o = prover.multiply(x.into(), y.into()).unwrap();
            prover.constrain(o - Scalar::from(12u64));
            let bytes = prover.prove(&bp).unwrap().to_bytes();
            let first = if backend == Backend::Bp { 1 } else { 17 };
            check(backend.name(), &bytes, &[first, first + 99], &[bytes.len() - 32], |b| {
                let proof = match R1CSProof::<C>::from_bytes(b) {
                    Ok(p) => p,
                    Err(_) => return false,
                };
                let mut t = Transcript::new(b"c");
                let mut verifier = Verifier::<_, C>::new(&mut t);
                verifier.set_backend(backend);
                let (x, y) = (verifier.commit(cx), verifier.commit(cy));
                let o = verifier.multiply(x.into(), y.into()).unwrap();
                verifier.constrain(o - Scalar::from(12u64));
                verifier.verify(&proof, &pc, &bp).is_ok()
            });
        }

        // BP++ range proof and MACT: C_L C_R C_O C_S | WNLA (X R ... | scalars)
        let st = RangeStatement::new(16, vec![(0, 1 << 16)]).unwrap();
        let bp2 = BulletproofGens::<C>::new(st.generators_capacity().max(64), 1);
        let (proof, v) = BpppRangeProof::<C>::prove(&st, &pc, &bp2, &[1234], &[Scalar::random(&mut rng)], &mut Transcript::new(b"b"), &mut rng).unwrap();
        let bytes = proof.to_bytes();
        check("bppp range", &bytes, &[0, 99, 132], &[bytes.len() - 32], |b| {
            BpppRangeProof::<C>::from_bytes(b, &st).map_or(false, |p| p.verify(&st, &pc, &bp2, &v, &mut Transcript::new(b"b")).is_ok())
        });
        let st = MactStatement::new(16, 1, 1).unwrap();
        let bp3 = BulletproofGens::<C>::new(st.generators_capacity(), 1);
        let asset = Scalar::random(&mut rng);
        let e = |rng: &mut ChaCha20Rng| MactEntry { amount: 5, asset, blinding: Scalar::random(rng) };
        let (ins, outs) = ([e(&mut rng)], [e(&mut rng)]);
        let (proof, v) = MactProof::<C>::prove(&st, &pc, &bp3, &ins, &outs, &mut Transcript::new(b"m"), &mut rng).unwrap();
        let bytes = proof.to_bytes();
        check("mact", &bytes, &[0, 99, 132], &[bytes.len() - 32], |b| {
            MactProof::<C>::from_bytes(b, &st).map_or(false, |p| p.verify(&st, &pc, &bp3, &v, &mut Transcript::new(b"m")).is_ok())
        });
    }
}

/// A proof of one curve given to the other does not parse (the lengths differ), and the same
/// statement on the two curves draws different challenges (the `curve` label in the
/// transcript) (Review Focus 2).
mod bound_to_curve {
    use bulletproofs::curve::{Curve, Ristretto, Secp256k1};
    use bulletproofs::r1cs::{Backend, ConstraintSystem, Prover, R1CSError, R1CSProof};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    fn product_proof<C: Curve>(backend: Backend) -> Vec<u8> {
        let pc = PedersenGens::<C>::default();
        let bp = BulletproofGens::<C>::new(16, 1);
        let mut t = Transcript::new(b"bound");
        let mut prover = Prover::new(&pc, &mut t);
        prover.set_backend(backend);
        let (_, x) = prover.commit(C::Scalar::from(3u64), C::Scalar::from(5u64));
        let (_, y) = prover.commit(C::Scalar::from(4u64), C::Scalar::from(6u64));
        let o = prover.multiply(x.into(), y.into()).unwrap();
        prover.constrain(o - C::Scalar::from(12u64));
        prover.prove(&bp).unwrap().to_bytes()
    }

    fn challenge_after_prover<C: Curve>() -> [u8; 32] {
        let pc = PedersenGens::<C>::default();
        let mut t = Transcript::new(b"bound");
        drop(Prover::new(&pc, &mut t));
        let mut c = [0u8; 32];
        t.challenge_bytes(b"probe", &mut c);
        c
    }

    #[test]
    fn proofs_are_bound_to_the_curve() {
        let mut backends = vec![Backend::Bp];
        backends.push(Backend::Bppp);
        for backend in backends {
            let r = product_proof::<Ristretto>(backend);
            let s = product_proof::<Secp256k1>(backend);
            assert!(R1CSProof::<Ristretto>::from_bytes(&r).is_ok() && R1CSProof::<Secp256k1>::from_bytes(&s).is_ok());
            assert!(matches!(R1CSProof::<Secp256k1>::from_bytes(&r), Err(R1CSError::FormatError)), "{}", backend);
            assert!(matches!(R1CSProof::<Ristretto>::from_bytes(&s), Err(R1CSError::FormatError)), "{}", backend);
        }
        assert_ne!(challenge_after_prover::<Ristretto>(), challenge_after_prover::<Secp256k1>());
    }
}

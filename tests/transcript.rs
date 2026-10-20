//! Transcripts: the generic interface, the SHA-256 transcript, its vectors.

#![allow(non_snake_case)]

use bulletproofs::{BulletproofGens, LinearProof, PedersenGens, RangeProof, Ristretto, TranscriptBackend};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

/// A backend that delegates to Merlin and counts the operations: proofs through it must equal
/// proofs through Merlin byte for byte.
#[derive(Clone)]
struct Counting(Transcript, usize);

impl Counting {
    fn new(label: &'static [u8]) -> Self {
        Counting(Transcript::new(label), 0)
    }
}

impl TranscriptBackend for Counting {
    fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        self.1 += 1;
        self.0.append_message(label, message)
    }
    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        self.1 += 1;
        self.0.append_u64(label, x)
    }
    fn challenge_bytes(&mut self, label: &'static [u8], dest: &mut [u8]) {
        self.1 += 1;
        self.0.challenge_bytes(label, dest)
    }
    fn build_rng(&self) -> merlin::TranscriptRngBuilder {
        self.0.build_rng()
    }
}

impl bulletproofs::TranscriptRef for Counting {
    type Backend = Self;
    fn backend(&mut self) -> &mut Self {
        self
    }
    fn backend_ref(&self) -> &Self {
        self
    }
}

/// Aggregated range proofs run the MPC dealer and the inner-product argument.
#[test]
fn a_delegating_backend_gives_merlin_range_proofs() {
    let (bp, pc) = (BulletproofGens::new(64, 2), PedersenGens::default());
    let blindings = [Scalar::from(1u8), Scalar::from(2u8)];
    let mut m = Transcript::new(b"t");
    let (merlin_proof, _) =
        RangeProof::prove_multiple_with_rng(&bp, &pc, &mut m, &[5, 9], &blindings, 32, &mut ChaCha20Rng::seed_from_u64(7)).unwrap();
    let mut c = Counting::new(b"t");
    let (counting_proof, v) =
        RangeProof::prove_multiple_with_rng(&bp, &pc, &mut c, &[5, 9], &blindings, 32, &mut ChaCha20Rng::seed_from_u64(7)).unwrap();
    assert_eq!(counting_proof.to_bytes(), merlin_proof.to_bytes());
    assert!(c.1 > 0);
    let mut cv = Counting::new(b"t");
    assert!(counting_proof.verify_multiple(&bp, &pc, &mut cv, &v, 32).is_ok());
    assert_eq!(cv.1, c.1);

    let mut m = Transcript::new(b"s");
    let (merlin_single, _) = RangeProof::prove_single_with_rng(&bp, &pc, &mut m, 3, &blindings[0], 8, &mut ChaCha20Rng::seed_from_u64(8)).unwrap();
    let (counting_single, v) =
        RangeProof::prove_single_with_rng(&bp, &pc, &mut Counting::new(b"s"), 3, &blindings[0], 8, &mut ChaCha20Rng::seed_from_u64(8)).unwrap();
    assert_eq!(counting_single.to_bytes(), merlin_single.to_bytes());
    assert!(counting_single.verify_single(&bp, &pc, &mut Counting::new(b"s"), &v, 8).is_ok());
}

#[test]
fn a_delegating_backend_gives_merlin_linear_proofs() {
    let n = 8;
    let bp = BulletproofGens::new(n, 1);
    let G: Vec<RistrettoPoint> = bp.share(0).G(n).cloned().collect();
    let pc = PedersenGens::default();
    let (F, B) = (pc.B, pc.B_blinding);
    let a: Vec<Scalar> = (0..n as u64).map(|i| Scalar::from(i + 3)).collect();
    let b: Vec<Scalar> = (0..n as u64).map(|i| Scalar::from(2 * i + 1)).collect();
    let r = Scalar::from(99u8);
    let c: Scalar = a.iter().zip(&b).map(|(x, y)| x * y).sum();
    let C = RistrettoPoint::vartime_multiscalar_mul(
        a.iter().chain(Some(&r)).chain(Some(&c)),
        G.iter().chain(Some(&B)).chain(Some(&F)),
    )
    .compress();
    let prove = |t: &mut dyn FnMut(&mut ChaCha20Rng) -> LinearProof<Ristretto>| t(&mut ChaCha20Rng::seed_from_u64(9));
    let merlin_proof = prove(&mut |rng| {
        LinearProof::<Ristretto>::create(&mut Transcript::new(b"l"), rng, &C, r, a.clone(), b.clone(), G.clone(), &F, &B).unwrap()
    });
    let counting_proof = prove(&mut |rng| {
        LinearProof::<Ristretto>::create(&mut Counting::new(b"l"), rng, &C, r, a.clone(), b.clone(), G.clone(), &F, &B).unwrap()
    });
    assert_eq!(counting_proof.to_bytes(), merlin_proof.to_bytes());
    assert!(counting_proof.verify(&mut Counting::new(b"l"), &C, &G, &F, &B, b).is_ok());
}

#[cfg(feature = "yoloproofs")]
mod r1cs {
    use super::*;
    use bulletproofs::r1cs::{Backend, ConstraintSystem, LinearCombination, Prover, R1CSProof, Verifier};
    use bulletproofs::TranscriptRef;
    use curve25519_dalek::ristretto::CompressedRistretto;

    /// `x · y = 15` with committed `x = 3`, `y = 5`; `bind` appends extra data through the
    /// constraint system's transcript, as a gadget would.
    fn product<CS: ConstraintSystem>(cs: &mut CS, x: Variable, y: Variable, bind: bool) {
        if bind {
            cs.transcript().append_message(b"ctx", b"gadget data");
        }
        let (_, _, o) = cs.multiply(x.into(), y.into());
        cs.constrain(LinearCombination::from(o) - Scalar::from(15u8));
    }

    use bulletproofs::r1cs::Variable;

    fn prove<T: TranscriptRef>(t: T, backend: Backend, bind: bool) -> (R1CSProof, Vec<CompressedRistretto>, T) {
        let (pc, bp) = (PedersenGens::default(), BulletproofGens::new(64, 1));
        let mut p = Prover::new(&pc, t);
        p.set_backend(backend);
        let (cx, x) = p.commit(Scalar::from(3u8), Scalar::from(11u8));
        let (cy, y) = p.commit(Scalar::from(5u8), Scalar::from(12u8));
        product(&mut p, x, y, bind);
        let (proof, t) = p.prove_with_rng_and_return_transcript(&bp, &mut ChaCha20Rng::seed_from_u64(5)).unwrap();
        (proof, vec![cx, cy], t)
    }

    fn verify<T: TranscriptRef>(t: T, backend: Backend, bind: bool, proof: &R1CSProof, V: &[CompressedRistretto]) -> Result<T, bulletproofs::r1cs::R1CSError> {
        let (pc, bp) = (PedersenGens::default(), BulletproofGens::new(64, 1));
        let mut v = Verifier::new(t);
        v.set_backend(backend);
        let x = v.commit(V[0]);
        let y = v.commit(V[1]);
        product(&mut v, x, y, bind);
        v.verify_and_return_transcript(proof, &pc, &bp)
    }

    fn equals_merlin(backend: Backend) {
        let (merlin_proof, V, _) = prove(Transcript::new(b"r"), backend, false);
        let mut c = Counting::new(b"r");
        let (counting_proof, _, _) = prove(&mut c, backend, false);
        assert_eq!(counting_proof.to_bytes(), merlin_proof.to_bytes());
        assert!(c.1 > 0);
        assert!(verify(&mut Counting::new(b"r"), backend, false, &counting_proof, &V).is_ok());
        assert!(verify(Transcript::new(b"r"), backend, false, &counting_proof, &V).is_ok());
    }

    #[test]
    fn r1cs_through_a_delegating_backend_equals_merlin() {
        equals_merlin(Backend::Bp);
    }

    #[cfg(feature = "bppp")]
    #[test]
    fn r1cs_bppp_backend_through_a_delegating_backend_equals_merlin() {
        equals_merlin(Backend::Bppp);
    }

    #[test]
    fn r1cs_transcript_is_usable_after_the_proof() {
        let (proof, V, mut pt) = prove(Counting::new(b"r"), Backend::Bp, false);
        let mut vt = verify(Counting::new(b"r"), Backend::Bp, false, &proof, &V).unwrap();
        let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
        pt.challenge_bytes(b"after", &mut a);
        vt.challenge_bytes(b"after", &mut b);
        assert_eq!(a, b);
        // bound to the proof: a fresh transcript gives another challenge
        let mut fresh = Counting::new(b"r");
        let mut f = [0u8; 32];
        fresh.challenge_bytes(b"after", &mut f);
        assert_ne!(a, f);
    }

    #[test]
    fn gadget_can_bind_extra_data() {
        let (proof, V, _) = prove(Counting::new(b"r"), Backend::Bp, true);
        assert!(verify(Counting::new(b"r"), Backend::Bp, true, &proof, &V).is_ok());
        assert!(verify(Counting::new(b"r"), Backend::Bp, false, &proof, &V).is_err());
    }
}

#[cfg(feature = "sha256-transcript")]
mod sha256 {
    use super::*;
    use bulletproofs::curve::{Curve, Field};
    use bulletproofs::Sha256Transcript;

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }

    /// Labels are `&'static`; the vectors' labels live for the test.
    fn leak(s: &str) -> &'static [u8] {
        Box::leak(unhex(s).into_boxed_slice())
    }

    fn scalar_hex<C: Curve>(t: &mut Sha256Transcript, label: &'static [u8]) -> String {
        let mut buf = [0u8; 64];
        t.challenge_bytes(label, &mut buf);
        hex(&C::Scalar::from_wide(&buf).to_bytes32())
    }

    #[test]
    fn sha256_transcript_matches_the_reference_kats() {
        let v: serde_json::Value = serde_json::from_str(include_str!("vectors/transcript/sha256.json")).unwrap();
        let mut checked = 0;
        for case in v["cases"].as_array().unwrap() {
            let mut t = Sha256Transcript::new(leak(case["label"].as_str().unwrap()));
            let expected = case["outputs"].as_array().unwrap();
            let mut k = 0;
            for op in case["ops"].as_array().unwrap() {
                let op = op.as_array().unwrap();
                let label = || leak(op[1].as_str().unwrap());
                let got = match op[0].as_str().unwrap() {
                    "append" => {
                        t.append_message(label(), &unhex(op[2].as_str().unwrap()));
                        continue;
                    }
                    "u64" => {
                        t.append_u64(label(), op[2].as_u64().unwrap());
                        continue;
                    }
                    "challenge" => {
                        let mut d = vec![0u8; op[2].as_u64().unwrap() as usize];
                        t.challenge_bytes(label(), &mut d);
                        hex(&d)
                    }
                    "scalar_ristretto" => scalar_hex::<Ristretto>(&mut t, label()),
                    #[cfg(feature = "secp256k1")]
                    "scalar_secp256k1" => scalar_hex::<bulletproofs::curve::Secp256k1>(&mut t, label()),
                    #[cfg(not(feature = "secp256k1"))]
                    "scalar_secp256k1" => {
                        let mut d = [0u8; 64];
                        t.challenge_bytes(label(), &mut d);
                        k += 1;
                        continue;
                    }
                    // the prover's RNG seed is not public; the next challenge checks that
                    // deriving it leaves the transcript unchanged
                    "rng_digest" => {
                        let _ = t.build_rng();
                        k += 1;
                        continue;
                    }
                    other => panic!("unknown op {}", other),
                };
                assert_eq!(got, expected[k].as_str().unwrap(), "case {} output {}", case["name"], k);
                k += 1;
                checked += 1;
            }
            assert_eq!(k, expected.len());
        }
        assert!(checked >= 20);
    }

    #[test]
    fn sha256_transcript_clone_replays() {
        let mut t = Sha256Transcript::new(b"clone");
        t.append_message(b"a", b"before the clone");
        let mut u = t.clone();
        let (mut x, mut y) = ([0u8; 64], [0u8; 64]);
        t.challenge_bytes(b"c", &mut x);
        u.challenge_bytes(b"c", &mut y);
        assert_eq!(x, y);
    }
}

/// Every protocol over both transcripts and both curves: prove and verify with one transcript;
/// the same proof fails under the other transcript type and under another label.
#[cfg(feature = "sha256-transcript")]
mod all_protocols {
    use bulletproofs::curve::ff::Field as _;
    use bulletproofs::curve::{Curve, Ristretto};
    use bulletproofs::{BulletproofGens, LinearProof, PedersenGens, RangeProof, Sha256Transcript, TranscriptBackend};
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    type Mk<T> = fn(&'static [u8]) -> T;

    fn sha(l: &'static [u8]) -> Sha256Transcript {
        Sha256Transcript::new(l)
    }

    fn mer(l: &'static [u8]) -> Transcript {
        Transcript::new(l)
    }

    /// Runs `$f::<C, T, U>` for both curves, with (SHA-256, Merlin) and (Merlin, SHA-256).
    macro_rules! both {
        ($name:ident, $f:ident) => {
            #[test]
            fn $name() {
                $f::<Ristretto, _, _>(sha, mer);
                $f::<Ristretto, _, _>(mer, sha);
                #[cfg(feature = "secp256k1")]
                {
                    $f::<bulletproofs::curve::Secp256k1, _, _>(sha, mer);
                    $f::<bulletproofs::curve::Secp256k1, _, _>(mer, sha);
                }
            }
        };
    }

    fn range<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(64, 4);
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let blind = C::Scalar::random(&mut rng);
        let (proof, com) = RangeProof::<C>::prove_single_with_rng(&bp, &pc, &mut t(b"rt"), 1_234_567, &blind, 32, &mut rng).unwrap();
        proof.verify_single(&bp, &pc, &mut t(b"rt"), &com, 32).unwrap();
        assert!(proof.verify_single(&bp, &pc, &mut u(b"rt"), &com, 32).is_err());
        assert!(proof.verify_single(&bp, &pc, &mut t(b"other"), &com, 32).is_err());
        let blinds: Vec<C::Scalar> = (0..4).map(|_| C::Scalar::random(&mut rng)).collect();
        let (p, coms) = RangeProof::<C>::prove_multiple_with_rng(&bp, &pc, &mut t(b"rt"), &[1, 2, 3, 4], &blinds, 16, &mut rng).unwrap();
        p.verify_multiple(&bp, &pc, &mut t(b"rt"), &coms, 16).unwrap();
        assert!(p.verify_multiple(&bp, &pc, &mut u(b"rt"), &coms, 16).is_err());
        assert!(p.verify_multiple(&bp, &pc, &mut t(b"other"), &coms, 16).is_err());
    }
    both!(sha256_range_round_trips_and_binds, range);

    /// The dealer verifies the shares with a clone of its initial transcript.
    fn mpc<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        use bulletproofs::range_proof_mpc::{dealer::Dealer, party::Party};
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(16, 2);
        let mut rng = ChaCha20Rng::seed_from_u64(6);
        let mut transcript = t(b"rt");
        let dealer = Dealer::new(&bp, &pc, &mut transcript, 16, 2).unwrap();
        let openings: Vec<(u64, C::Scalar)> = [7u64, 300].iter().map(|&v| (v, C::Scalar::random(&mut rng))).collect();
        let coms: Vec<C::Compressed> = openings.iter().map(|(v, r)| C::compress(&pc.commit(C::Scalar::from(*v), *r))).collect();
        let parties: Vec<_> = openings.iter().map(|&(v, r)| Party::new(&bp, &pc, v, r, 16).unwrap()).collect();
        let (parties, bits): (Vec<_>, Vec<_>) = parties.into_iter().enumerate().map(|(j, p)| p.assign_position_with_rng(j, &mut rng).unwrap()).unzip();
        let (dealer, y) = dealer.receive_bit_commitments(bits).unwrap();
        let (parties, polys): (Vec<_>, Vec<_>) = parties.into_iter().map(|p| p.apply_challenge_with_rng(&y, &mut rng)).unzip();
        let (dealer, x) = dealer.receive_poly_commitments(polys).unwrap();
        let shares: Vec<_> = parties.into_iter().map(|p| p.apply_challenge(&x).unwrap()).collect();
        let proof = dealer.receive_shares_with_rng(&shares, &mut rng).unwrap();
        proof.verify_multiple(&bp, &pc, &mut t(b"rt"), &coms, 16).unwrap();
        assert!(proof.verify_multiple(&bp, &pc, &mut u(b"rt"), &coms, 16).is_err());
        assert!(proof.verify_multiple(&bp, &pc, &mut t(b"other"), &coms, 16).is_err());
    }
    both!(sha256_mpc_round_trips_and_binds, mpc);

    fn linear<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let n = 8;
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(n, 1);
        let G: Vec<C::Point> = bp.share(0).G(n).cloned().collect();
        let a: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let b: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let c: C::Scalar = a.iter().zip(&b).map(|(x, y)| *x * y).sum();
        let r = C::Scalar::random(&mut rng);
        let (mut s, mut pts) = (a.clone(), G.clone());
        s.extend([r, c]);
        pts.extend([pc.B_blinding, pc.B]);
        let com = C::compress(&C::msm_vt(&s, &pts));
        let proof = LinearProof::<C>::create(&mut t(b"rt"), &mut rng, &com, r, a, b.clone(), G.clone(), &pc.B, &pc.B_blinding).unwrap();
        proof.verify(&mut t(b"rt"), &com, &G, &pc.B, &pc.B_blinding, b.clone()).unwrap();
        assert!(proof.verify(&mut u(b"rt"), &com, &G, &pc.B, &pc.B_blinding, b.clone()).is_err());
        assert!(proof.verify(&mut t(b"other"), &com, &G, &pc.B, &pc.B_blinding, b).is_err());
    }
    both!(sha256_linear_round_trips_and_binds, linear);

    /// `x · y = 15` and, in the second phase, `(x - z)(y - z) = 15 - 8z + z²` for a challenge
    /// `z`, with committed `x = 3`, `y = 5`.
    #[cfg(feature = "yoloproofs")]
    fn r1cs_with<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>, backend: bulletproofs::r1cs::Backend, two_phase: bool) {
        use bulletproofs::r1cs::{lc, ConstraintSystem as _, Prover, RandomizableConstraintSystem, RandomizedConstraintSystem, Variable, Verifier};
        fn gadget<C: Curve, CS: RandomizableConstraintSystem<C::Scalar>>(cs: &mut CS, x: Variable, y: Variable, two_phase: bool) {
            let (_, _, o) = cs.multiply(lc(x), lc(y));
            cs.constrain(lc(o) - C::Scalar::from(15u64));
            if two_phase {
                cs.specify_randomized_constraints(move |cs| {
                    let z = cs.challenge_scalar(b"z");
                    let (_, _, o) = cs.multiply(lc(x) - z, lc(y) - z);
                    cs.constrain(lc(o) - (C::Scalar::from(15u64) - C::Scalar::from(8u64) * z + z * z));
                    Ok(())
                })
                .unwrap();
            }
        }
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(16, 1);
        let mut rng = ChaCha20Rng::seed_from_u64(8);
        let mut pt = t(b"rt");
        let mut p = Prover::new(&pc, &mut pt);
        p.set_backend(backend);
        let (cx, x) = p.commit(C::Scalar::from(3u64), C::Scalar::random(&mut rng));
        let (cy, y) = p.commit(C::Scalar::from(5u64), C::Scalar::random(&mut rng));
        gadget::<C, _>(&mut p, x, y, two_phase);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
        let run = |label: &'static [u8], other_type: bool| -> bool {
            macro_rules! go {
                ($tr:expr) => {{
                    let mut tr = $tr;
                    let mut v = Verifier::<_, C>::for_curve(&mut tr);
                    v.set_backend(backend);
                    let x = v.commit(cx);
                    let y = v.commit(cy);
                    gadget::<C, _>(&mut v, x, y, two_phase);
                    v.verify(&proof, &pc, &bp).is_ok()
                }};
            }
            if other_type {
                go!(u(label))
            } else {
                go!(t(label))
            }
        };
        assert!(run(b"rt", false));
        assert!(!run(b"rt", true));
        assert!(!run(b"other", false));
    }

    #[cfg(feature = "yoloproofs")]
    fn r1cs_bp<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        r1cs_with::<C, T, U>(t, u, bulletproofs::r1cs::Backend::Bp, false);
        r1cs_with::<C, T, U>(t, u, bulletproofs::r1cs::Backend::Bp, true);
    }
    #[cfg(feature = "yoloproofs")]
    both!(sha256_r1cs_bp_round_trips_and_binds, r1cs_bp);

    /// R1CS on BP++ runs the reciprocal argument (and its norm argument) under the transcript;
    /// one phase only (BP++ has no randomized constraints).
    #[cfg(all(feature = "yoloproofs", feature = "bppp"))]
    fn r1cs_bppp<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        r1cs_with::<C, T, U>(t, u, bulletproofs::r1cs::Backend::Bppp, false);
    }
    #[cfg(all(feature = "yoloproofs", feature = "bppp"))]
    both!(sha256_r1cs_bppp_round_trips_and_binds, r1cs_bppp);

    #[cfg(feature = "bppp")]
    fn bppp_range<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        use bulletproofs::bppp::{BatchVerifier, RangeProof, RangeStatement};
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let st = RangeStatement::new(16, vec![(0, 1 << 32), (10, 1000)]).unwrap();
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(st.generators_capacity(), 1);
        let blinds: Vec<C::Scalar> = (0..2).map(|_| C::Scalar::random(&mut rng)).collect();
        let (proof, V) = RangeProof::<C>::prove(&st, &pc, &bp, &[123_456, 999], &blinds, &mut t(b"rt"), &mut rng).unwrap();
        proof.verify(&st, &pc, &bp, &V, &mut t(b"rt")).unwrap();
        assert!(proof.verify(&st, &pc, &bp, &V, &mut u(b"rt")).is_err());
        assert!(proof.verify(&st, &pc, &bp, &V, &mut t(b"other")).is_err());
        // batch verification, with the right and the wrong transcripts
        let mut batch = BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(10));
        batch.add_range(&proof, &st, &V, &mut t(b"rt")).unwrap();
        batch.verify().unwrap();
        let mut batch = BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(10));
        let added = batch.add_range(&proof, &st, &V, &mut u(b"rt"));
        assert!(added.is_err() || batch.verify().is_err());
    }
    #[cfg(feature = "bppp")]
    both!(sha256_bppp_range_and_batch_round_trip_and_bind, bppp_range);

    #[cfg(feature = "bppp")]
    fn bppp_mact<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        use bulletproofs::bppp::{MactEntry, MactProof, MactStatement};
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        let st = MactStatement::new(16, 2, 2).unwrap();
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(st.generators_capacity(), 1);
        let (a, b) = (C::Scalar::random(&mut rng), C::Scalar::random(&mut rng));
        let e = |amount: u64, asset: C::Scalar, rng: &mut ChaCha20Rng| MactEntry { amount, asset, blinding: C::Scalar::random(rng) };
        let inputs = [e(40, a, &mut rng), e(7, b, &mut rng)];
        let outputs = [e(40, a, &mut rng), e(7, b, &mut rng)];
        let (proof, V) = MactProof::<C>::prove(&st, &pc, &bp, &inputs, &outputs, &mut t(b"rt"), &mut rng).unwrap();
        proof.verify(&st, &pc, &bp, &V, &mut t(b"rt")).unwrap();
        assert!(proof.verify(&st, &pc, &bp, &V, &mut u(b"rt")).is_err());
        assert!(proof.verify(&st, &pc, &bp, &V, &mut t(b"other")).is_err());
    }
    #[cfg(feature = "bppp")]
    both!(sha256_bppp_mact_round_trips_and_binds, bppp_mact);

    /// The arithmetic-circuit protocol: `n` products `w_L w_R = w_O` and one linear row each.
    #[cfg(feature = "bppp")]
    fn bppp_circuit<C: Curve, T: TranscriptBackend + Clone, U: TranscriptBackend>(t: Mk<T>, u: Mk<U>) {
        use bulletproofs::bppp::{ArithmeticCircuit, BpppGens, CircuitProof, CircuitWitness, Slot, SparseMatrix};
        let n = 4;
        let mut rng = ChaCha20Rng::seed_from_u64(12);
        let w_l: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let w_r: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let w_o: Vec<C::Scalar> = w_l.iter().zip(&w_r).map(|(a, b)| *a * b).collect();
        let w: Vec<C::Scalar> = w_l.iter().chain(&w_r).chain(&w_o).copied().collect();
        let mut m_l = SparseMatrix::new(3 * n);
        let mut a_l = Vec::new();
        for i in 0..n {
            let terms: Vec<(usize, C::Scalar)> = [i, n + (i + 1) % n, 2 * n + (i + 2) % n].iter().map(|c| (*c, C::Scalar::random(&mut rng))).collect();
            a_l.push(-terms.iter().map(|(c, v)| *v * w[*c]).sum::<C::Scalar>());
            m_l.push_row(terms);
        }
        let mut m_m = SparseMatrix::new(3 * n);
        for i in 0..n {
            m_m.push_row(vec![(2 * n + i, C::Scalar::ONE)]);
        }
        let c = ArithmeticCircuit {
            n_m: n,
            n_o: n,
            n_v: 1,
            n_lin: 0,
            k: 0,
            w_l: m_l,
            a_l,
            w_m: m_m,
            a_m: vec![C::Scalar::ZERO; n],
            f_l: false,
            f_m: false,
            partition: (0..n).map(|i| (Slot::NormO, i)).collect(),
        };
        let wit = CircuitWitness { w_l, w_r, w_o, v: vec![], s: vec![] };
        let pc = PedersenGens::<C>::for_curve();
        let bp = BulletproofGens::<C>::for_curve(8, 1);
        let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
        let p = CircuitProof::<C>::prove(&c, &gens, &[], &wit, &mut t(b"rt"), &mut rng).unwrap();
        p.verify(&c, &gens, &[], &mut t(b"rt")).unwrap();
        assert!(p.verify(&c, &gens, &[], &mut u(b"rt")).is_err());
        assert!(p.verify(&c, &gens, &[], &mut t(b"other")).is_err());
    }
    #[cfg(feature = "bppp")]
    both!(sha256_bppp_circuit_round_trips_and_binds, bppp_circuit);

    /// BP and BP++ range proofs over an Elements commitment (a blinded asset generator).
    #[cfg(all(feature = "secp256k1", feature = "bppp"))]
    #[test]
    fn sha256_elements_range_round_trips_and_binds() {
        use bulletproofs::curve::Secp256k1;
        use bulletproofs::elements;
        let mut rng = ChaCha20Rng::seed_from_u64(13);
        let asset = elements::generator_generate_blinded(&[0x42; 32], &k256::Scalar::random(&mut rng));
        let pc = PedersenGens::<Secp256k1>::with_value_generator(asset);
        let (value, blinding) = (21_000_000u64, k256::Scalar::random(&mut rng));
        let bp = BulletproofGens::<Secp256k1>::for_curve(64, 1);
        let (proof, v) = RangeProof::<Secp256k1>::prove_single_with_rng(&bp, &pc, &mut sha(b"rt"), value, &blinding, 64, &mut rng).unwrap();
        proof.verify_single(&bp, &pc, &mut sha(b"rt"), &v, 64).unwrap();
        assert!(proof.verify_single(&bp, &pc, &mut mer(b"rt"), &v, 64).is_err());
        assert!(proof.verify_single(&bp, &pc, &mut sha(b"other"), &v, 64).is_err());
        let st = bulletproofs::bppp::RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
        let bp2 = BulletproofGens::<Secp256k1>::for_curve(st.generators_capacity(), 1);
        let (p, V) = bulletproofs::bppp::RangeProof::<Secp256k1>::prove(&st, &pc, &bp2, &[value], &[blinding], &mut sha(b"rt"), &mut rng).unwrap();
        assert_eq!(V, vec![v]);
        p.verify(&st, &pc, &bp2, &V, &mut sha(b"rt")).unwrap();
        assert!(p.verify(&st, &pc, &bp2, &V, &mut mer(b"rt")).is_err());
    }
}

/// Full secp256k1 proofs under the SHA-256 transcript with the trace of every message and
/// challenge (`tests/vectors/transcript/secp256k1-*.json`): test vectors for a Simplicity
/// verifier. `ref/sha256_transcript.py --check-trace` recomputes the challenges independently.
#[cfg(all(feature = "secp256k1", feature = "bppp", feature = "yoloproofs"))]
mod full_proofs {
    use bulletproofs::curve::{Curve, PointEncoding, Secp256k1};
    use bulletproofs::r1cs::{lc, Backend, ConstraintSystem, Prover, R1CSProof, Variable, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens, Sha256Transcript, TranscriptBackend};
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use serde_json::{json, Value};

    const LABEL: &[u8] = b"bulletproofs-vectors";

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    /// Records every operation of the backend it wraps.
    #[derive(Clone)]
    struct Recording<T: TranscriptBackend> {
        inner: T,
        trace: Vec<Value>,
    }

    impl Recording<Sha256Transcript> {
        fn new() -> Self {
            Recording { inner: Sha256Transcript::new(LABEL), trace: Vec::new() }
        }
    }

    impl<T: TranscriptBackend> TranscriptBackend for Recording<T> {
        fn append_message(&mut self, label: &'static [u8], m: &[u8]) {
            self.trace.push(json!(["append", hex(label), hex(m)]));
            self.inner.append_message(label, m)
        }
        // recorded as the append of le64(x) it is
        fn append_u64(&mut self, label: &'static [u8], x: u64) {
            self.trace.push(json!(["append", hex(label), hex(&x.to_le_bytes())]));
            self.inner.append_u64(label, x)
        }
        fn challenge_bytes(&mut self, label: &'static [u8], d: &mut [u8]) {
            self.inner.challenge_bytes(label, d);
            self.trace.push(json!(["challenge", hex(label), d.len(), hex(d)]));
        }
        fn build_rng(&self) -> merlin::TranscriptRngBuilder {
            self.inner.build_rng()
        }
    }

    type S = <Secp256k1 as Curve>::Scalar;

    fn path(name: &str) -> String {
        format!("{}/tests/vectors/transcript/secp256k1-{}.json", env!("CARGO_MANIFEST_DIR"), name)
    }

    fn vector(name: &str, protocol: &str, statement: Value, proof: &[u8], trace: Vec<Value>) -> Value {
        json!({"protocol": protocol, "curve": "secp256k1", "label": hex(LABEL), "seed": 1,
               "statement": statement, "proof": hex(proof), "trace": trace, "name": name})
    }

    /// A 64-bit BP++ range proof of `0x0123456789abcdef`.
    fn bppp_range() -> Value {
        use bulletproofs::bppp::{RangeProof, RangeStatement};
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
        let pc = PedersenGens::<Secp256k1>::for_curve();
        let bp = BulletproofGens::<Secp256k1>::for_curve(st.generators_capacity(), 1);
        let blinding = <S as bulletproofs::curve::ff::Field>::random(&mut rng);
        let mut t = Recording::new();
        let (proof, V) = RangeProof::<Secp256k1>::prove(&st, &pc, &bp, &[0x0123_4567_89ab_cdef], &[blinding], &mut t, &mut rng).unwrap();
        let bytes = proof.to_bytes();
        // the verifier absorbs and squeezes exactly what the prover did
        let mut v = Recording::new();
        RangeProof::<Secp256k1>::from_bytes(&bytes, &st).unwrap().verify(&st, &pc, &bp, &V, &mut v).unwrap();
        assert_eq!(v.trace, t.trace);
        let statement = json!({"base": 16, "ranges": [["0", "18446744073709551616"]], "commitments": V.iter().map(|c| hex(c.as_bytes())).collect::<Vec<_>>()});
        vector("bppp-range", "bppp range proof", statement, &bytes, t.trace)
    }

    /// `x · y = 15` with committed `x = 3`, `y = 5`.
    fn product<CS: ConstraintSystem<S>>(cs: &mut CS, x: Variable, y: Variable) {
        let (_, _, o) = cs.multiply(lc(x), lc(y));
        cs.constrain(lc(o) - S::from(15u64));
    }

    fn r1cs(backend: Backend, name: &str) -> Value {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let pc = PedersenGens::<Secp256k1>::for_curve();
        let bp = BulletproofGens::<Secp256k1>::for_curve(16, 1);
        let random = |rng: &mut ChaCha20Rng| <S as bulletproofs::curve::ff::Field>::random(rng);
        let mut t = Recording::new();
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(backend);
        let (cx, x) = p.commit(S::from(3u64), random(&mut rng));
        let (cy, y) = p.commit(S::from(5u64), random(&mut rng));
        product(&mut p, x, y);
        let bytes = p.prove_with_rng(&bp, &mut rng).unwrap().to_bytes();
        let mut vt = Recording::new();
        let mut v = Verifier::<_, Secp256k1>::for_curve(&mut vt);
        v.set_backend(backend);
        let (x, y) = (v.commit(cx), v.commit(cy));
        product(&mut v, x, y);
        v.verify(&R1CSProof::<Secp256k1>::from_bytes(&bytes).unwrap(), &pc, &bp).unwrap();
        assert_eq!(vt.trace, t.trace);
        let statement = json!({"circuit": "x * y = 15", "commitments": [hex(cx.as_bytes()), hex(cy.as_bytes())]});
        vector(name, &format!("r1cs ({:?} backend)", backend), statement, &bytes, t.trace)
    }

    fn all() -> Vec<(&'static str, Value)> {
        vec![("bppp-range", bppp_range()), ("r1cs-bppp", r1cs(Backend::Bppp, "r1cs-bppp")), ("r1cs-bp", r1cs(Backend::Bp, "r1cs-bp"))]
    }

    #[test]
    fn sha256_full_proof_vectors_are_stable() {
        for (name, got) in all() {
            let file: Value = serde_json::from_str(&std::fs::read_to_string(path(name)).expect("vector file")).unwrap();
            assert_eq!(got, file, "vector {} changed", name);
            assert!(!unhex(file["proof"].as_str().unwrap()).is_empty());
        }
    }

    #[test]
    #[ignore]
    fn regenerate_sha256_full_proof_vectors() {
        for (name, v) in all() {
            std::fs::write(path(name), serde_json::to_string_pretty(&v).unwrap() + "\n").unwrap();
        }
    }
}

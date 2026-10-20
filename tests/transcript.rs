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

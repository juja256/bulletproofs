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

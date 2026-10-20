//! The `bulletproofs::secp256k1` facade: a BP++ 64-bit range proof, a BP range proof and an
//! R1CS proof over secp256k1 without naming the curve parameter.

#![cfg(all(feature = "secp256k1", feature = "bppp", feature = "yoloproofs"))]

use bulletproofs::curve::ff::Field;
use bulletproofs::secp256k1::{self, BulletproofGens, PedersenGens, Scalar};
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

#[test]
fn facade_proves_and_verifies() {
    let mut rng = ChaCha20Rng::seed_from_u64(12);
    let pc = PedersenGens::for_curve();
    let st = bulletproofs::bppp::RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
    let bp = BulletproofGens::for_curve(st.generators_capacity().max(64), 1);
    let blinding = Scalar::random(&mut rng);
    let (proof, v) = secp256k1::bppp::RangeProof::prove(&st, &pc, &bp, &[u64::MAX], &[blinding], &mut Transcript::new(b"f"), &mut rng).unwrap();
    secp256k1::bppp::RangeProof::from_bytes(&proof.to_bytes(), &st).unwrap().verify(&st, &pc, &bp, &v, &mut Transcript::new(b"f")).unwrap();

    let (proof, v) = secp256k1::RangeProof::prove_single(&bp, &pc, &mut Transcript::new(b"g"), 7, &blinding, 64).unwrap();
    secp256k1::RangeProof::from_bytes(&proof.to_bytes()).unwrap().verify_single(&bp, &pc, &mut Transcript::new(b"g"), &v, 64).unwrap();

    let mut t = Transcript::new(b"h");
    let mut prover = secp256k1::r1cs::Prover::new(&pc, &mut t);
    let (c, x) = prover.commit(Scalar::from(9u64), blinding);
    use bulletproofs::r1cs::ConstraintSystem;
    let (_, _, o) = prover.multiply(x.into(), x.into());
    prover.constrain(o - Scalar::from(81u64));
    let proof = prover.prove(&bp).unwrap();
    let mut t = Transcript::new(b"h");
    let mut verifier = secp256k1::r1cs::Verifier::for_curve(&mut t);
    let x = verifier.commit(c);
    let (_, _, o) = verifier.multiply(x.into(), x.into());
    verifier.constrain(o - Scalar::from(81u64));
    verifier.verify(&secp256k1::r1cs::R1CSProof::from_bytes(&proof.to_bytes()).unwrap(), &pc, &bp).unwrap();
}

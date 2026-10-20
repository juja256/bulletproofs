//! Range proofs over Elements / secp256k1-zkp Pedersen commitments: `value * A + r * G` for a
//! (blinded) asset generator `A`, exchanged in secp256k1-zkp's 33-byte encoding.

#![cfg(all(feature = "secp256k1", feature = "bppp"))]

use bulletproofs::bppp::{RangeProof as BpppRangeProof, RangeStatement};
use bulletproofs::curve::ff::Field;
use bulletproofs::curve::{Curve, Secp256k1};
use bulletproofs::elements;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use k256::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

#[test]
fn range_proofs_over_elements_commitments() {
    let mut rng = ChaCha20Rng::seed_from_u64(14);
    // a blinded asset generator, as in a confidential transaction output
    let asset = elements::generator_generate_blinded(&[0x42; 32], &Scalar::random(&mut rng));
    let pc = PedersenGens::<Secp256k1>::with_value_generator(asset);
    let (value, blinding) = (21_000_000u64, Scalar::random(&mut rng));
    // the commitment as Elements publishes it
    let published = elements::commitment_serialize(&elements::commit(value, &blinding, &asset)).unwrap();
    let commitment = Secp256k1::compress(&elements::commitment_parse(&published).unwrap());

    // BP: 64-bit range proof; the prover's commitment is the Elements one
    let bp = BulletproofGens::<Secp256k1>::for_curve(64, 1);
    let (proof, v) =
        RangeProof::<Secp256k1>::prove_single_with_rng(&bp, &pc, &mut Transcript::new(b"elements"), value, &blinding, 64, &mut rng).unwrap();
    assert_eq!(v, commitment);
    proof.verify_single(&bp, &pc, &mut Transcript::new(b"elements"), &commitment, 64).unwrap();

    // BP++: a range proof over the same commitment
    let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
    let bp2 = BulletproofGens::<Secp256k1>::for_curve(st.generators_capacity(), 1);
    let (proof, v) = BpppRangeProof::<Secp256k1>::prove(&st, &pc, &bp2, &[value], &[blinding], &mut Transcript::new(b"e"), &mut rng).unwrap();
    assert_eq!(v, vec![commitment]);
    let parsed = BpppRangeProof::<Secp256k1>::from_bytes(&proof.to_bytes(), &st).unwrap();
    parsed.verify(&st, &pc, &bp2, &[commitment], &mut Transcript::new(b"e")).unwrap();

    // another asset's generator does not verify the commitment
    let other = PedersenGens::<Secp256k1>::with_value_generator(elements::generator_generate(&[0x43; 32]));
    assert!(parsed.verify(&st, &other, &bp2, &[commitment], &mut Transcript::new(b"e")).is_err());
    // the default generators are H (the explicit value generator of secp256k1-zkp)
    let h = PedersenGens::<Secp256k1>::with_value_generator(elements::h());
    let d = PedersenGens::<Secp256k1>::for_curve();
    assert_eq!((h.B, h.B_blinding), (d.B, d.B_blinding));
}

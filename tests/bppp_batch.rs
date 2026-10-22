//! Batch verification of BP++ proofs (spec §3.11): a mixed batch verifies, one bad proof
//! anywhere makes it fail, a statement that cannot be replayed is an error when added (one that
//! replays fails in `verify`).

#![allow(non_snake_case)]

use bulletproofs::bppp::{self, BatchVerifier, MactEntry, MactStatement, RangeStatement};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use bulletproofs::curve::Ristretto;

enum Item {
    Range(bppp::RangeProof<Ristretto>, RangeStatement, Vec<CompressedRistretto>),
    Mact(bppp::MactProof<Ristretto>, MactStatement, Vec<CompressedRistretto>),
}

fn items(pc: &PedersenGens<Ristretto>, bp: &BulletproofGens<Ristretto>) -> Vec<Item> {
    let mut rng = ChaCha20Rng::seed_from_u64(5);
    let mut out = Vec::new();
    for (base, ranges, values) in [
        (16u64, vec![(0u64, 1u128 << 64)], vec![0x0123_4567_89ab_cdefu64]),
        (256, vec![(0, 1 << 64)], vec![77]),
        (4, vec![(10, 1000), (0, 1 << 32)], vec![500, 123_456]),
        (2, vec![(0, 2)], vec![1]),
    ] {
        let st = RangeStatement::new(base, ranges).unwrap();
        let s: Vec<Scalar> = values.iter().map(|_| Scalar::random(&mut rng)).collect();
        let (p, V) = bppp::RangeProof::prove(&st, pc, bp, &values, &s, &mut Transcript::new(b"batch"), &mut rng).unwrap();
        out.push(Item::Range(p, st, V));
    }
    let st = MactStatement::new(16, 2, 1).unwrap();
    let e = |amount: u64, asset: u64, s: u64| MactEntry { amount, asset: Scalar::from(asset), blinding: Scalar::from(s) };
    let (p, V) = bppp::MactProof::prove(&st, pc, bp, &[e(70, 9, 1), e(30, 9, 2)], &[e(100, 9, 3)], &mut Transcript::new(b"batch"), &mut rng).unwrap();
    out.push(Item::Mact(p, st, V));
    out
}

fn batch(pc: &PedersenGens<Ristretto>, bp: &BulletproofGens<Ristretto>, items: &[Item], seed: u64) -> Result<(), bulletproofs::ProofError> {
    let mut b = BatchVerifier::new(pc, bp, ChaCha20Rng::seed_from_u64(seed));
    for it in items {
        match it {
            Item::Range(p, st, V) => b.add_range(p, st, V, &mut Transcript::new(b"batch"))?,
            Item::Mact(p, st, V) => b.add_mact(p, st, V, &mut Transcript::new(b"batch"))?,
        }
    }
    b.verify()
}

#[test]
fn mixed_batch_verifies() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(512, 1);
    let it = items(&pc, &bp);
    for it in &it {
        match it {
            Item::Range(p, st, V) => p.verify(st, &pc, &bp, V, &mut Transcript::new(b"batch")).unwrap(),
            Item::Mact(p, st, V) => p.verify(st, &pc, &bp, V, &mut Transcript::new(b"batch")).unwrap(),
        }
    }
    batch(&pc, &bp, &it, 1).unwrap();
    batch(&pc, &bp, &it[..1], 2).unwrap();
    batch(&pc, &bp, &[], 3).unwrap();
    // an empty batch needs no generators
    BatchVerifier::new(&pc, &BulletproofGens::new(1, 1), ChaCha20Rng::seed_from_u64(4)).verify().unwrap();
}

/// Replace input commitment `V_0` of item `i` by another valid commitment: its own check fails,
/// and so does every batch that contains it, whatever the weights.
#[test]
fn one_bad_proof_fails_the_batch() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(512, 1);
    for i in 0..5 {
        let mut it = items(&pc, &bp);
        let other = pc.commit(Scalar::from(5u64), Scalar::from(6u64)).compress();
        match &mut it[i] {
            Item::Range(_, _, V) | Item::Mact(_, _, V) => V[0] = other,
        }
        for seed in 0..4 {
            assert!(batch(&pc, &bp, &it, seed).is_err(), "item {} seed {}", i, seed);
        }
    }
}

/// A transcript that differs (another statement) or too few generators: an error at once.
#[test]
fn wrong_statements_are_errors_when_added() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(512, 1);
    let it = items(&pc, &bp);
    let mut b = BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(0));
    if let Item::Range(p, st, V) = &it[2] {
        assert!(b.add_range(p, st, &V[..1], &mut Transcript::new(b"batch")).is_err(), "too few inputs");
        let other = RangeStatement::new(4, vec![(10, 1001), (0, 1 << 32)]).unwrap();
        b.add_range(p, &other, V, &mut Transcript::new(b"batch")).unwrap(); // replays fine, fails in the MSM
    }
    assert!(b.verify().is_err());
    let small = BulletproofGens::new(8, 1);
    let mut b = BatchVerifier::new(&pc, &small, ChaCha20Rng::seed_from_u64(0));
    if let Item::Range(p, st, V) = &it[0] {
        assert!(b.add_range(p, st, V, &mut Transcript::new(b"batch")).is_err(), "generators");
    }
}

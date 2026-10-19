//! Malformed BP++ proofs (fuzz-style, deterministic): flipped, truncated, extended and random
//! bytes are parse errors or proofs that do not verify, never panics.

#![allow(non_snake_case)]

use bulletproofs::bppp::{self, MactEntry, MactStatement, RangeStatement};
use bulletproofs::r1cs::{Backend, CircuitBuilder, ConstraintSystem, Prover, R1CSProof, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// Mutations of `good`: one flipped byte, a truncation, an extension, a swapped 32-byte
/// block, and random strings of nearby lengths.
fn mutations(good: &[u8], rng: &mut ChaCha20Rng, n: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..n {
        let mut x = good.to_vec();
        match rng.gen_range(0..5) {
            0 => {
                let i = rng.gen_range(0..x.len());
                x[i] ^= 1 << rng.gen_range(0..8);
            }
            1 => x.truncate(rng.gen_range(0..x.len())),
            2 => x.extend((0..rng.gen_range(1..70)).map(|_| rng.gen::<u8>())),
            3 if x.len() >= 64 => {
                let (i, j) = (rng.gen_range(0..x.len() / 32), rng.gen_range(0..x.len() / 32));
                for k in 0..32 {
                    x.swap(32 * i + k, 32 * j + k);
                }
            }
            _ => x = (0..rng.gen_range(0..good.len() + 64)).map(|_| rng.gen::<u8>()).collect(),
        }
        if x != good {
            out.push(x);
        }
    }
    out
}

#[test]
fn range_and_mact_proofs() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(512, 1);
    let mut rng = ChaCha20Rng::seed_from_u64(11);
    for base in [16u64, 256] {
        let st = RangeStatement::new(base, vec![(0, 1 << 64), (5, 1000)]).unwrap();
        let (p, V) = bppp::RangeProof::prove(&st, &pc, &bp, &[42, 999], &[Scalar::ONE, Scalar::ONE], &mut Transcript::new(b"m"), &mut rng).unwrap();
        let good = p.to_bytes();
        assert!(bppp::RangeProof::from_bytes(&good, &st).unwrap().verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).is_ok());
        for x in mutations(&good, &mut rng, 400) {
            if let Ok(q) = bppp::RangeProof::from_bytes(&x, &st) {
                assert!(q.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).is_err());
            }
        }
    }
    let st = MactStatement::new(16, 1, 1).unwrap();
    let e = |a: u64, s: u64| MactEntry { amount: a, asset: Scalar::from(3u64), blinding: Scalar::from(s) };
    let (p, V) = bppp::MactProof::prove(&st, &pc, &bp, &[e(9, 1)], &[e(9, 2)], &mut Transcript::new(b"m"), &mut rng).unwrap();
    let good = p.to_bytes();
    for x in mutations(&good, &mut rng, 400) {
        if let Ok(q) = bppp::MactProof::from_bytes(&x, &st) {
            assert!(q.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).is_err());
        }
    }
}

fn gadget<CS: CircuitBuilder>(cs: &mut CS, x: bulletproofs::r1cs::Variable, v: Option<u64>) {
    let t = cs.table((0..16u64).map(|i| vec![i]).collect(), &[4]).unwrap();
    let a = cs.lookup_value(t, v.map(|v| v & 15)).unwrap();
    let b = cs.lookup_value(t, v.map(|v| v >> 4)).unwrap();
    cs.constrain(x - a - b * Scalar::from(16u64));
    let (l, _, _) = cs.multiply(a.into(), b.into());
    cs.constrain(l - a);
}

#[test]
fn r1cs_proofs_of_every_kind() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(256, 1);
    let mut rng = ChaCha20Rng::seed_from_u64(12);
    for (backend, builder) in [(Backend::Bp, true), (Backend::Bppp, false), (Backend::Bppp, true)] {
        let mut t = Transcript::new(b"r");
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(backend);
        let (V, x) = p.commit(Scalar::from(0x5au64), Scalar::from(7u64));
        if builder {
            gadget(&mut p, x, Some(0x5a));
        } else {
            let (_, _, o) = p.multiply(x.into(), Scalar::from(2u64).into());
            p.constrain(o - Scalar::from(0xb4u64));
        }
        let good = p.prove_with_rng(&bp, &mut rng).unwrap().to_bytes();
        let verify = |proof: &R1CSProof| {
            let mut t = Transcript::new(b"r");
            let mut v = Verifier::new(&mut t);
            v.set_backend(backend);
            let x = v.commit(V);
            if builder {
                gadget(&mut v, x, None);
            } else {
                let (_, _, o) = v.multiply(x.into(), Scalar::from(2u64).into());
                v.constrain(o - Scalar::from(0xb4u64));
            }
            v.verify(proof, &pc, &bp)
        };
        verify(&R1CSProof::from_bytes(&good).unwrap()).unwrap();
        for x in mutations(&good, &mut rng, 300) {
            if let Ok(q) = R1CSProof::from_bytes(&x) {
                assert!(verify(&q).is_err(), "{:?} builder {}", backend, builder);
            }
        }
    }
    // random strings starting with every tag
    for tag in 0u8..6 {
        for len in [0usize, 1, 9, 17, 18, 100, 200, 400] {
            let mut x: Vec<u8> = (0..len).map(|_| rng.gen()).collect();
            if !x.is_empty() {
                x[0] = tag;
            }
            let _ = R1CSProof::from_bytes(&x);
        }
    }
    // huge dimensions in the BP++ headers
    for tag in [2u8, 3] {
        for (a, b) in [(u64::MAX, 1), (1 << 62, 0), (0, 0), (1, u64::MAX), (1 << 40, 1 << 40)] {
            let mut x = vec![tag];
            x.extend(a.to_le_bytes());
            x.extend(b.to_le_bytes());
            x.extend([0u8; 300]);
            assert!(R1CSProof::from_bytes(&x).is_err());
        }
    }
}

#[test]
fn wnla_and_circuit_from_bytes() {
    let mut rng = ChaCha20Rng::seed_from_u64(13);
    for _ in 0..500 {
        let len = rng.gen_range(0..1500);
        let x: Vec<u8> = (0..len).map(|_| rng.gen()).collect();
        let (a, b) = (rng.gen_range(0..300), rng.gen_range(0..300));
        let _ = bppp::WnlaProof::from_bytes(&x, a, b);
    }
    let _ = CompressedRistretto([0xff; 32]).decompress();
}

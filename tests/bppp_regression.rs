//! Regression pins for BP++ proofs with a fixed RNG: the SHA3-256 of the proof bytes of every
//! front end. Optimisations must not change them; a deliberate format change updates them
//! (and says so in the commit). Not golden vectors in the BP sense yet: the format is not frozen.

#![allow(non_snake_case)]

use bulletproofs::bppp::{self, ArithmeticCircuit, BpppGens, CircuitWitness, MactEntry, MactStatement, RangeStatement, Slot, SparseMatrix};
use bulletproofs::r1cs::{Backend, CircuitBuilder, ConstraintSystem, LinearCombination, Prover, Variable};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use sha3::{Digest, Sha3_256};

fn h(bytes: &[u8]) -> String {
    hex::encode(Sha3_256::digest(bytes))
}

fn rng(seed: u64) -> ChaCha20Rng {
    ChaCha20Rng::seed_from_u64(seed)
}

/// `n` multiplications `w_L w_R = w_O` and `n` linear rows of three terms, from a seed.
fn circuit(n: usize, seed: u64) -> (ArithmeticCircuit, CircuitWitness) {
    let mut r = rng(seed);
    let s = |r: &mut ChaCha20Rng| Scalar::random(r);
    let w_l: Vec<Scalar> = (0..n).map(|_| s(&mut r)).collect();
    let w_r: Vec<Scalar> = (0..n).map(|_| s(&mut r)).collect();
    let w_o: Vec<Scalar> = w_l.iter().zip(&w_r).map(|(a, b)| a * b).collect();
    let w: Vec<Scalar> = w_l.iter().chain(&w_r).chain(&w_o).copied().collect();
    let mut m_l = SparseMatrix::new(3 * n);
    let mut a_l = Vec::new();
    for i in 0..n {
        let cols = [i, n + (i * 7 + 1) % n, 2 * n + (i * 13 + 5) % n];
        let terms: Vec<(usize, Scalar)> = cols.iter().map(|c| (*c, s(&mut r))).collect();
        a_l.push(-terms.iter().map(|(c, v)| v * w[*c]).sum::<Scalar>());
        m_l.push_row(terms);
    }
    let mut m_m = SparseMatrix::new(3 * n);
    for i in 0..n {
        m_m.push_row(vec![(2 * n + i, Scalar::ONE)]);
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
        a_m: vec![Scalar::ZERO; n],
        f_l: false,
        f_m: false,
        partition: (0..n).map(|i| (Slot::NormO, i)).collect(),
    };
    (c, CircuitWitness { w_l, w_r, w_o, v: vec![], s: vec![] })
}

fn circuit_proof(n: usize) -> Vec<u8> {
    let (c, w) = circuit(n, n as u64);
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(n.max(6), 1);
    let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
    let p = bppp::circuit::prove(&c, &gens, &[], &w, &mut Transcript::new(b"reg"), &mut rng(1)).unwrap();
    p.verify(&c, &gens, &[], &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

fn range_proof(base: u64) -> Vec<u8> {
    let st = RangeStatement::new(base, vec![(0, 1 << 64), (1000, 1u128 << 40)]).unwrap();
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(st.generators_capacity(), 1);
    let (p, V) = bppp::RangeProof::prove(&st, &pc, &bp, &[0x0123_4567_89ab_cdef, 123_456_789], &[Scalar::from(5u64), Scalar::from(6u64)], &mut Transcript::new(b"reg"), &mut rng(2)).unwrap();
    p.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

fn mact_proof() -> Vec<u8> {
    let st = MactStatement::new(16, 2, 2).unwrap();
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(st.generators_capacity(), 1);
    let e = |amount: u64, asset: u64, s: u64| MactEntry { amount, asset: Scalar::from(asset), blinding: Scalar::from(s) };
    let (ins, outs) = ([e(100, 1, 1), e(50, 2, 2)], [e(100, 1, 3), e(50, 2, 4)]);
    let (p, V) = bppp::MactProof::prove(&st, &pc, &bp, &ins, &outs, &mut Transcript::new(b"reg"), &mut rng(3)).unwrap();
    p.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

/// The R1CS front end: plain constraint system (spec §6) or with builder operations (§7).
fn r1cs_proof(builder: bool) -> Vec<u8> {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(1024, 1);
    let mut t = Transcript::new(b"reg");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let (_, x) = p.commit(Scalar::from(0xbeefu64), Scalar::from(9u64));
    let (_, y) = p.commit(Scalar::from(3u64), Scalar::from(10u64));
    let (_, _, o) = p.multiply(x.into(), y.into());
    p.constrain(o - Scalar::from(3 * 0xbeefu64));
    if builder {
        let byte = p.table((0..256u64).map(|v| vec![v]).collect(), &[8]).unwrap();
        let mut sum = LinearCombination::default();
        for i in 0..2 {
            let b = p.lookup_value(byte, Some((0xbeef >> (8 * i)) & 255)).unwrap();
            sum = sum + b * Scalar::from(1u64 << (8 * i));
        }
        p.constrain(sum - x);
        let w = p.witness(Some(Scalar::from(7u64))).unwrap();
        p.product(w.into(), y.into(), Scalar::from(21u64).into()).unwrap();
        let mut r = p.reciprocal(&[252]).unwrap();
        r.add_weighted(x.into(), vec![Variable::Committed(1).into()]);
        r.add_public(LinearCombination::from(-Scalar::from(0xbeefu64)), vec![3]);
        p.finish_reciprocal(r).unwrap();
    }
    p.prove_with_rng(&bp, &mut rng(4)).unwrap().to_bytes()
}

#[test]
fn bppp_proofs_are_pinned() {
    let got = [
        ("circuit 2^4", h(&circuit_proof(16))),
        ("circuit 2^8", h(&circuit_proof(256))),
        ("range base 16", h(&range_proof(16))),
        ("range base 256 (shared)", h(&range_proof(256))),
        ("mact 2x2", h(&mact_proof())),
        ("r1cs §6", h(&r1cs_proof(false))),
        ("builder §7", h(&r1cs_proof(true))),
    ];
    let want: [&str; 7] = [
        "91080da4e4d50c29fff3e01e18363ae76f57d2e81db442c414d08156f99712ec",
        "4e0dcba54dcc55dc6b3b1722cb8b64da4b0734c32b3b9a46b933cb621735ff15",
        "016aa2b521af9a13094d465cac4ae2f19d17b98b00da4a1f3487d62d9dcab4ee",
        "3b61627a206703a65a48187c73559cfc02585e89a89b3672d9756a5fe7842373",
        "cfb42059fbfa5264b6136c16d7bccb20047444825d6234f93b184466fd86b5d3",
        "c75a29c28b2178c0de11e85941fdd26888fe9b4ddcd8f22f4d1f0f02faecde17",
        "772b2ba4e8de836a35b57cdc079ac7d782ff7e3ab84ff734babeb98edcd3d06f",
    ];
    for (name, g) in &got {
        println!("{}: {}", name, g);
    }
    for ((name, g), w) in got.iter().zip(want) {
        assert_eq!(g, w, "{}", name);
    }
}

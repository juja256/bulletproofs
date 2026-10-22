//! Regression pins for BP++ proofs with a fixed RNG: the SHA3-256 of the proof bytes of every
//! front end. Optimisations must not change them; a deliberate format change updates them
//! (and says so in the commit). Not golden vectors in the BP sense yet: the format is not frozen.

#![allow(non_snake_case)]

use bulletproofs::bppp::{self, ArithmeticCircuit, BpppGens, CircuitWitness, MactEntry, MactStatement, RangeStatement, Slot, SparseMatrix};
use bulletproofs::r1cs::{Backend, ConstraintSystem, LinearCombination, Prover};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use sha3::{Digest, Sha3_256};
use bulletproofs::curve::Ristretto;

fn h(bytes: &[u8]) -> String {
    hex::encode(Sha3_256::digest(bytes))
}

fn rng(seed: u64) -> ChaCha20Rng {
    ChaCha20Rng::seed_from_u64(seed)
}

/// `n` multiplications `w_L w_R = w_O` and `n` linear rows of three terms, from a seed.
fn circuit(n: usize, seed: u64) -> (ArithmeticCircuit<Scalar>, CircuitWitness<Scalar>) {
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
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(n.max(6), 1);
    let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
    let p = bppp::CircuitProof::prove(&c, &gens, &[], &w, &mut Transcript::new(b"reg"), &mut rng(1)).unwrap();
    p.verify(&c, &gens, &[], &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

fn range_proof(base: u64) -> Vec<u8> {
    let st = RangeStatement::new(base, vec![(0, 1 << 64), (1000, 1u128 << 40)]).unwrap();
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(st.generators_capacity(), 1);
    let (p, V) = bppp::RangeProof::prove(&st, &pc, &bp, &[0x0123_4567_89ab_cdef, 123_456_789], &[Scalar::from(5u64), Scalar::from(6u64)], &mut Transcript::new(b"reg"), &mut rng(2)).unwrap();
    p.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

fn mact_proof() -> Vec<u8> {
    let st = MactStatement::new(16, 2, 2).unwrap();
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(st.generators_capacity(), 1);
    let e = |amount: u64, asset: u64, s: u64| MactEntry { amount, asset: Scalar::from(asset), blinding: Scalar::from(s) };
    let (ins, outs) = ([e(100, 1, 1), e(50, 2, 2)], [e(100, 1, 3), e(50, 2, 4)]);
    let (p, V) = bppp::MactProof::prove(&st, &pc, &bp, &ins, &outs, &mut Transcript::new(b"reg"), &mut rng(3)).unwrap();
    p.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"reg")).unwrap();
    p.to_bytes()
}

/// The R1CS front end: plain constraint system or with builder operations (spec §6.2: one
/// protocol and encoding for both; pins changed with option B).
fn r1cs_proof(builder: bool) -> Vec<u8> {
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(1024, 1);
    let mut t = Transcript::new(b"reg");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let (_, x) = p.commit(Scalar::from(0xbeefu64), Scalar::from(9u64));
    let (_, y) = p.commit(Scalar::from(3u64), Scalar::from(10u64));
    let o = p.multiply(x.into(), y.into()).unwrap();
    p.constrain(o - Scalar::from(3 * 0xbeefu64));
    if builder {
        let byte = p.table((0..256u64).map(|v| vec![v]).collect()).unwrap();
        let mut sum = LinearCombination::default();
        for i in 0..2 {
            let b = p.lookup_value(byte, Some((0xbeef >> (8 * i)) & 255)).unwrap();
            sum = sum + b * Scalar::from(1u64 << (8 * i));
        }
        p.constrain(sum - x);
        let w = p.witness(Some(Scalar::from(7u64))).unwrap();
        p.constrain_product(w.into(), y.into(), Scalar::from(21u64).into()).unwrap();
        let r = p.reciprocal(1).unwrap();
        r.add_weighted(&mut p, x.into(), &[y.into()]).unwrap();
        r.add_public(&mut p, LinearCombination::from(-Scalar::from(0xbeefu64)), &[3]).unwrap();
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
        "15028aab7946ac21d4b1bae04ef149261a623151293fbb1d31ca08de6f51cdd0",
        "ebb2104f71a77d994f5127546617a38d1c8a20c3674f3f40e39038c18b82ff62",
        "8ffe2a23d9fc9ab7a56602c7de5ef5424f1ed87db14ac7b08fecdb65d1613653",
        "2a48d4d8030d829f69b59399816e9bad94c0723e6eb09f8ada733f04ccd1c176",
        "c0901efd7fa5282e8e55cb0b79016df2a5b7265869b63d88b0df2d28bc4fb713",
        "21078855863d69b79787eb06eff4da666c2267a5e07fdd33b4beb59427b6db0a",
        // 2026-10-22: the witness `w` of the product is folded into its left wire
        "1fb847f35ff5f3c2e275a0acab75dfec1085c088b8b4a3f7371344dca119149b",
    ];
    for (name, g) in &got {
        println!("{}: {}", name, g);
    }
    for ((name, g), w) in got.iter().zip(want) {
        assert_eq!(g, w, "{}", name);
    }
}

/// An RNG that returns only zeros.
struct ZeroRng;
impl rand_chacha::rand_core::RngCore for ZeroRng {
    fn next_u32(&mut self) -> u32 {
        0
    }
    fn next_u64(&mut self) -> u64 {
        0
    }
    fn fill_bytes(&mut self, d: &mut [u8]) {
        d.iter_mut().for_each(|x| *x = 0)
    }
    fn try_fill_bytes(&mut self, d: &mut [u8]) -> Result<(), rand_chacha::rand_core::Error> {
        self.fill_bytes(d);
        Ok(())
    }
}
impl rand_chacha::rand_core::CryptoRng for ZeroRng {}

/// The prover's randomness is mixed with the circuit digest and the witness (spec §1): with
/// a broken RNG, two witnesses with the same `w_O` (left and right inputs swapped) still get
/// different blindings of `C_O`; the same witness gives the same proof.
#[test]
fn prover_randomness_depends_on_the_witness() {
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(16, 1);
    let n = 8;
    let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
    let (mut c, w1) = circuit(n, 3);
    c.w_l = SparseMatrix::new(3 * n);
    c.a_l = vec![];
    let w2 = CircuitWitness { w_l: w1.w_r.clone(), w_r: w1.w_l.clone(), ..w1.clone() };
    let prove = |w: &CircuitWitness<Scalar>| bppp::CircuitProof::prove(&c, &gens, &[], w, &mut Transcript::new(b"z"), &mut ZeroRng).unwrap();
    let (p1, p2) = (prove(&w1), prove(&w2));
    assert_ne!(p1.C_O, p2.C_O);
    assert_eq!(prove(&w1), p1);
    p2.verify(&c, &gens, &[], &mut Transcript::new(b"z")).unwrap();
}

/// The prover's randomness is bound to the live transcript (found in review): with a broken
/// RNG, the same circuit and witness proven in two contexts must not reuse blindings (that
/// would leak the witness through the different challenges).
#[test]
fn prover_randomness_binds_the_transcript_context() {
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(16, 1);
    let gens = BpppGens::new(&pc, &bp, 0, 8).unwrap();
    let (c, w) = circuit(8, 4);
    let p1 = bppp::CircuitProof::prove(&c, &gens, &[], &w, &mut Transcript::new(b"A"), &mut ZeroRng).unwrap();
    let p2 = bppp::CircuitProof::prove(&c, &gens, &[], &w, &mut Transcript::new(b"B"), &mut ZeroRng).unwrap();
    assert_ne!(p1.C_L, p2.C_L);
    assert_ne!(p1.C_O, p2.C_O);
    let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
    let bp = BulletproofGens::new(st.generators_capacity(), 1);
    let (r1, _) = bppp::RangeProof::prove(&st, &pc, &bp, &[5], &[Scalar::ONE], &mut Transcript::new(b"A"), &mut ZeroRng).unwrap();
    let (r2, _) = bppp::RangeProof::prove(&st, &pc, &bp, &[5], &[Scalar::ONE], &mut Transcript::new(b"B"), &mut ZeroRng).unwrap();
    assert_ne!(r1.to_bytes()[..64], r2.to_bytes()[..64]);
}

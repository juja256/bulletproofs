//! Shared helpers for the test-vector tests (`tests/vectors/bppp/*.json`).

use alloc::vec::Vec;
use core::convert::TryInto;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use serde_json::Value;

use super::circuit::{CircuitProof, Slot};
use super::gens::BpppGens;
use super::reciprocal::{self, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness};
use super::sparse::SparseMatrix;
use super::transcript::Replay;
use crate::{BulletproofGens, PedersenGens};

/// Hands out the given scalars to `Scalar::random` (32 bytes little-endian, then 32 zero
/// bytes: the wide reduction returns the scalar itself).
pub struct ScalarRng(alloc::collections::VecDeque<u8>);

impl ScalarRng {
    pub fn new(scalars: &[Scalar]) -> Self {
        let mut q = alloc::collections::VecDeque::new();
        for s in scalars {
            q.extend(s.to_bytes().iter());
            q.extend([0u8; 32].iter());
        }
        ScalarRng(q)
    }
}

impl rand_core::RngCore for ScalarRng {
    fn next_u32(&mut self) -> u32 {
        unimplemented!()
    }
    fn next_u64(&mut self) -> u64 {
        unimplemented!()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.iter_mut().for_each(|b| *b = self.0.pop_front().expect("more randomness than in the vector"));
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl rand_core::CryptoRng for ScalarRng {}

pub fn sc(v: &Value) -> Scalar {
    let b: [u8; 32] = hex::decode(v.as_str().unwrap()).unwrap().try_into().unwrap();
    Scalar::from_canonical_bytes(b).unwrap()
}

pub fn scs(v: &Value) -> Vec<Scalar> {
    v.as_array().unwrap().iter().map(sc).collect()
}

/// A decimal string or a number.
pub fn int(v: &Value) -> u128 {
    match v {
        Value::String(s) => s.parse().unwrap(),
        _ => v.as_u64().unwrap() as u128,
    }
}

fn sparse_from(v: &Value, cols: usize) -> SparseMatrix {
    let mut m = SparseMatrix::new(cols);
    for row in v.as_array().unwrap() {
        m.push_row(row.as_array().unwrap().iter().map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]))));
    }
    m
}

fn pole(v: &Value) -> Option<Scalar> {
    if v.is_null() {
        None
    } else {
        Some(sc(v))
    }
}

fn slot(s: &str) -> Slot {
    match s {
        "nO" => Slot::NormO,
        "lO" => Slot::LinO,
        "lL" => Slot::LinL,
        "lR" => Slot::LinR,
        _ => panic!("slot {}", s),
    }
}

/// The reciprocal circuit stored in a vector case.
pub fn recip_circuit(case: &Value) -> ReciprocalCircuit {
    let u = |k: &str| case[k].as_u64().unwrap() as usize;
    let (n_p, n_m, n_o) = (u("n_p"), u("n_m"), u("n_o"));
    let n_w = 2 * (n_p + n_m) + n_o;
    ReciprocalCircuit {
        n_p,
        n_m,
        n_o,
        n_v: u("n_v"),
        n_lin: u("n_lin"),
        k: u("k"),
        w_n: sparse_from(&case["w_n"], n_w),
        a_n: scs(&case["a_n"]),
        w_m: sparse_from(&case["w_m"], n_w),
        a_m: scs(&case["a_m"]),
        w_l: sparse_from(&case["w_l"], n_w),
        a_l: scs(&case["a_l"]),
        recip: case["recip"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| ReciprocalRow {
                terms: r["terms"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]), pole(&t[2])))
                    .collect(),
                consts: r["consts"].as_array().unwrap().iter().map(|t| (sc(&t[0]), pole(&t[1]))).collect(),
            })
            .collect(),
        f_l: u("f_l") == 1,
        f_m: u("f_m") == 1,
        partition: case["partition"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| (slot(p[0].as_str().unwrap()), p[1].as_u64().unwrap() as usize))
            .collect(),
    }
}

/// The reciprocal witness stored in a vector case.
pub fn recip_witness(case: &Value) -> ReciprocalWitness {
    ReciprocalWitness {
        w_d: scs(&case["w_D"]),
        w_l: scs(&case["w_L"]),
        w_r: scs(&case["w_R"]),
        w_o: scs(&case["w_O"]),
        v: case["v"].as_array().unwrap().iter().map(scs).collect(),
        s: scs(&case["s"]),
    }
}

/// Prove the case's circuit with its randomness and challenges (without the prover's
/// satisfiability check), compare every reciprocal, commitment and norm-argument round with
/// the vector, and check both verdicts. Returns the proof.
pub fn run_recip_case(case: &Value, c: &ReciprocalCircuit, w: &ReciprocalWitness) -> CircuitProof {
    let name = case["name"].as_str().unwrap();
    let ch = &case["chal"];
    let alpha = sc(&ch["alpha"]);
    let satisfied = case["satisfied"].as_bool().unwrap();
    assert_eq!(c.is_satisfied(w, alpha), satisfied, "{}: satisfied", name);
    assert_eq!(c.reciprocals_for_test(w, alpha), scs(&case["w_P"]), "{}: w_P", name);
    let (n_mm, n_lin) = (c.n_p + c.n_m, c.n_lin);
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(n_mm.max(n_lin + 6), 1);
    let g = BpppGens::new(&pc, &bp, n_lin, n_mm).unwrap();
    let point = |p: &Value| {
        (g.g * sc(&p["g"]) + RistrettoPoint::multiscalar_mul(scs(&p["h"]), &g.h) + RistrettoPoint::multiscalar_mul(scs(&p["n"]), g.n))
            .compress()
    };
    let V: Vec<CompressedRistretto> = w.v.iter().zip(&w.s).map(|(v, s)| g.commit_input(v, *s).compress()).collect();
    for (i, p) in case["V"].as_array().unwrap().iter().enumerate() {
        assert_eq!(V[i], point(p), "{}: V_{}", name, i);
    }
    let r = &case["rand"];
    let randomness: Vec<Scalar> = ["r_O", "r_L", "r_R", "l_S", "n_S"].iter().flat_map(|k| scs(&r[*k])).collect();
    let challenges: Vec<Scalar> =
        ["alpha", "rho", "lambda", "beta", "delta", "tau"].iter().map(|k| sc(&ch[*k])).chain(scs(&case["gammas"])).collect();
    let proof = reciprocal::prove_impl(c, &g, &V, w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness), false)
        .unwrap();
    let checked = reciprocal::prove(c, &g, &V, w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness));
    assert_eq!(checked.is_ok(), satisfied, "{}: prover check", name);
    assert_eq!(proof.C_L, point(&case["C_L"]), "{}: C_L", name);
    assert_eq!(proof.C_R, point(&case["C_R"]), "{}: C_R", name);
    assert_eq!(proof.C_O, point(&case["C_O"]), "{}: C_O", name);
    assert_eq!(proof.C_S, point(&case["C_S"]), "{}: C_S", name);
    let rounds = case["rounds"].as_array().unwrap();
    assert_eq!(proof.wnla.X.len(), rounds.len(), "{}: rounds", name);
    for (i, round) in rounds.iter().enumerate() {
        assert_eq!(proof.wnla.X[i], point(&round["X"]), "{}: X_{}", name, i);
        assert_eq!(proof.wnla.R[i], point(&round["R"]), "{}: R_{}", name, i);
    }
    assert_eq!(proof.wnla.l, scs(&case["l_final"]), "{}: l", name);
    assert_eq!(proof.wnla.n, scs(&case["n_final"]), "{}: n", name);
    let verdict = reciprocal::verify(&proof, c, &g, &V, &mut Replay::new(challenges)).is_ok();
    assert_eq!(verdict, case["verifies"].as_bool().unwrap(), "{}: verdict", name);
    proof
}

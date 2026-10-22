//! Shared helpers for the test-vector tests (`tests/vectors/bppp/*.json`).

use alloc::vec::Vec;
use core::convert::TryInto;

use curve25519_dalek::scalar::Scalar;
use ff::Field as _;
use serde_json::Value;

use super::circuit::{CircuitProof, Slot};
use super::gens::BpppGens;
use super::reciprocal::{self, Component, Pole, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness, TuplePole};
use super::sparse::SparseMatrix;
use super::transcript::Replay;
use crate::curve::{Curve, Field};
use crate::{BulletproofGens, PedersenGens};

/// How `Field::random` turns RNG bytes into a scalar, so that [`ScalarRng`] can hand out given
/// scalars.
pub trait TestScalar: Field {
    /// The bytes `Self::random` reads to return `self`.
    fn random_bytes(&self) -> Vec<u8>;
}

/// dalek: 64 bytes, little-endian, reduced (32 bytes of the scalar, then 32 zero bytes).
impl TestScalar for Scalar {
    fn random_bytes(&self) -> Vec<u8> {
        let mut b = self.to_bytes().to_vec();
        b.extend([0u8; 32].iter());
        b
    }
}

/// k256: 32 big-endian bytes, rejection sampling (a canonical encoding is accepted at once).
impl TestScalar for k256::Scalar {
    fn random_bytes(&self) -> Vec<u8> {
        self.to_bytes32().to_vec()
    }
}

/// The JSON vectors of `name` for the curve `C` (`tests/vectors/bppp/` for ristretto255,
/// `tests/vectors/bppp/secp256k1/` for secp256k1).
pub fn vectors<C: Curve>(ristretto: &'static str, secp256k1: &'static str) -> Value {
    let text = if C::NAME == "ristretto255" { ristretto } else { secp256k1 };
    serde_json::from_str(text).unwrap()
}

/// `n` generators from the label: `C::point_from_uniform(SHA3-512(label || i))` (for
/// ristretto255 the same as `RistrettoPoint::hash_from_bytes::<Sha3_512>`).
pub fn label_gens<C: Curve>(label: &str, n: usize) -> Vec<C::Point> {
    use sha3::{Digest, Sha3_512};
    (0..n)
        .map(|i| {
            let h: [u8; 64] = Sha3_512::digest(alloc::format!("{label}{i}").as_bytes()).into();
            C::point_from_uniform(&h)
        })
        .collect()
}

/// `g G + <h, H> + <n, N>` for a symbolic point of the reference (`{"g", "h", "n"}`).
pub fn sym_point<C: Curve>(p: &Value, g: &C::Point, h: &[C::Point], n: &[C::Point]) -> C::Compressed {
    let (sh, sn) = (scs::<C::Scalar>(&p["h"]), scs::<C::Scalar>(&p["n"]));
    C::compress(&(*g * sc::<C::Scalar>(&p["g"]) + C::msm_vt(&sh, &h[..sh.len()]) + C::msm_vt(&sn, &n[..sn.len()])))
}

/// Hands out the given scalars to `Scalar::random` (32 bytes little-endian, then 32 zero
/// bytes: the wide reduction returns the scalar itself).
pub struct ScalarRng(alloc::collections::VecDeque<u8>);

impl ScalarRng {
    pub fn new<F: TestScalar>(scalars: &[F]) -> Self {
        ScalarRng(scalars.iter().flat_map(|s| s.random_bytes()).collect())
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

pub fn sc<F: Field>(v: &Value) -> F {
    let b: [u8; 32] = hex::decode(v.as_str().unwrap()).unwrap().try_into().unwrap();
    F::from_bytes32(&b).unwrap()
}

pub fn scs<F: Field>(v: &Value) -> Vec<F> {
    v.as_array().unwrap().iter().map(sc).collect()
}

/// A decimal string or a number.
pub fn int(v: &Value) -> u128 {
    match v {
        Value::String(s) => s.parse().unwrap(),
        _ => v.as_u64().unwrap() as u128,
    }
}

pub fn sparse_from<F: Field>(v: &Value, cols: usize) -> SparseMatrix<F> {
    let mut m = SparseMatrix::new(cols);
    for row in v.as_array().unwrap() {
        m.push_row(row.as_array().unwrap().iter().map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]))));
    }
    m
}

/// `null`, one scalar (a constant pole, v1 cases) or a list of scalars (a pole polynomial).
fn pole<F: Field>(v: &Value) -> Option<Pole<F>> {
    match v {
        Value::Null => None,
        Value::Array(_) => Some(Pole(scs(v))),
        _ => Some(sc::<F>(v).into()),
    }
}

/// The tuple poles of a case (`[[i, [[terms, const], ...]], ...]`; absent: none).
fn tuples<F: Field>(v: &Value) -> Vec<TuplePole<F>> {
    v.as_array()
        .map(|a| {
            a.iter()
                .map(|e| TuplePole {
                    pole: e[0].as_u64().unwrap() as usize,
                    components: e[1]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|x| Component {
                            terms: x[0].as_array().unwrap().iter().map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]))).collect(),
                            constant: sc(&x[1]),
                        })
                        .collect(),
                })
                .collect()
        })
        .unwrap_or_default()
}

pub fn slot(s: &str) -> Slot {
    match s {
        "nO" => Slot::NormO,
        "lO" => Slot::LinO,
        "lL" => Slot::LinL,
        "lR" => Slot::LinR,
        _ => panic!("slot {}", s),
    }
}

/// The reciprocal circuit stored in a vector case.
pub fn recip_circuit<F: Field>(case: &Value) -> ReciprocalCircuit<F> {
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
        tuples: tuples(&case["tuples"]),
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
pub fn recip_witness<F: Field>(case: &Value) -> ReciprocalWitness<F> {
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
pub fn run_recip_case<C: Curve>(case: &Value, c: &ReciprocalCircuit<C::Scalar>, w: &ReciprocalWitness<C::Scalar>) -> CircuitProof<C>
where
    C::Scalar: TestScalar,
{
    let name = case["name"].as_str().unwrap();
    let ch = &case["chal"];
    let alpha: C::Scalar = sc(&ch["alpha"]);
    let uses_eta = case["uses_eta"].as_bool().unwrap_or(false);
    assert_eq!(c.uses_eta(), uses_eta, "{}: uses eta", name);
    let eta = if uses_eta { sc(&ch["eta"]) } else { C::Scalar::ZERO };
    if !case["digest"].is_null() {
        assert_eq!(hex::encode(c.digest()), case["digest"].as_str().unwrap(), "{}: digest", name);
    }
    if uses_eta {
        assert_eq!(c.poles_for_test(w, eta), scs(&case["w_D_eta"]), "{}: w_D at eta", name);
    }
    let satisfied = case["satisfied"].as_bool().unwrap();
    assert_eq!(c.is_satisfied(w, eta, alpha), satisfied, "{}: satisfied", name);
    assert_eq!(c.reciprocals_for_test(w, eta, alpha), scs(&case["w_P"]), "{}: w_P", name);
    let (n_mm, n_lin) = (c.n_p + c.n_m, c.n_lin);
    let pc = PedersenGens::<C>::for_curve();
    let bp = BulletproofGens::<C>::for_curve(super::gens::capacity(n_lin, n_mm), 1);
    let g = BpppGens::new(&pc, &bp, n_lin, n_mm).unwrap();
    let point = |p: &Value| sym_point::<C>(p, &g.g, &g.h, g.n);
    let V: Vec<C::Compressed> = w.v.iter().zip(&w.s).map(|(v, s)| C::compress(&g.commit_input(v, *s))).collect();
    for (i, p) in case["V"].as_array().unwrap().iter().enumerate() {
        assert_eq!(V[i], point(p), "{}: V_{}", name, i);
    }
    let r = &case["rand"];
    let randomness: Vec<C::Scalar> = ["r_O", "r_L", "r_R", "l_S", "n_S"].iter().flat_map(|k| scs(&r[*k])).collect();
    let names: &[&str] = if uses_eta { &["eta", "alpha", "rho", "lambda", "beta", "delta", "tau"] } else { &["alpha", "rho", "lambda", "beta", "delta", "tau"] };
    let challenges: Vec<C::Scalar> = names.iter().map(|k| sc(&ch[*k])).chain(scs(&case["gammas"])).collect();
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

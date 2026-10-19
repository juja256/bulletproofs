//! Replays the builder programs of `tests/vectors/bppp/builder.json` (independent Python
//! reference, spec §7) through `Prover` and `Verifier`: construction errors at the same
//! operation, the lowered reciprocal form circuit and witness column for column, the costs,
//! the commitments (as for `reciprocal.json`), and real proofs with both backends.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::Value;

use super::builder::{CircuitBuilder, Cost, TableId};
use super::{Backend, ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier};
use crate::bppp::testutil;
use crate::{BulletproofGens, PedersenGens};

fn var(v: &Value) -> Variable {
    let a = v.as_array().unwrap();
    let i = || a[1].as_u64().unwrap() as usize;
    match a[0].as_str().unwrap() {
        "V" => Variable::Committed(i()),
        "L" => Variable::MultiplierLeft(i()),
        "R" => Variable::MultiplierRight(i()),
        "O" => Variable::MultiplierOutput(i()),
        "W" => Variable::Witness(i()),
        "1" => Variable::One(),
        x => panic!("variable {}", x),
    }
}

fn lc(v: &Value) -> LinearCombination {
    v.as_array().unwrap().iter().map(|t| (var(&t[0]), testutil::sc(&t[1]))).collect()
}

fn lcs(v: &Value) -> Vec<LinearCombination> {
    v.as_array().unwrap().iter().map(lc).collect()
}

fn ints(v: &Value) -> Vec<u64> {
    v.as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect()
}

fn widths(v: &Value) -> Vec<u32> {
    ints(v).into_iter().map(|x| x as u32).collect()
}

/// Run the program; `commit(cs, v, s)` commits an input. Returns the index and error of the
/// first failing operation.
fn run<CS: CircuitBuilder>(
    cs: &mut CS,
    program: &[Value],
    prover: bool,
    commit: &mut dyn FnMut(&mut CS, Scalar, Scalar) -> Variable,
) -> Result<(), (usize, R1CSError)> {
    let val = |op: &Value, k: &str| if prover { Some(testutil::sc(&op[k])) } else { None };
    for (i, op) in program.iter().enumerate() {
        let r: Result<(), R1CSError> = (|| {
            match op["op"].as_str().unwrap() {
                "commit" => {
                    commit(cs, testutil::sc(&op["v"]), testutil::sc(&op["s"]));
                }
                "multiply" => {
                    cs.multiply(lc(&op["l"]), lc(&op["r"]));
                }
                "allocate" => {
                    cs.allocate(val(op, "v"))?;
                }
                "allocate_multiplier" => {
                    cs.allocate_multiplier(if prover { Some((testutil::sc(&op["l"]), testutil::sc(&op["r"]))) } else { None })?;
                }
                "constrain" => cs.constrain(lc(&op["lc"])),
                "witness" => {
                    cs.witness(val(op, "v"))?;
                }
                "product" => cs.product(lc(&op["l"]), lc(&op["r"]), lc(&op["out"]))?,
                "table" => {
                    let rows: Vec<Vec<u64>> = op["rows"].as_array().unwrap().iter().map(ints).collect();
                    cs.table(rows, &widths(&op["widths"]))?;
                }
                "lookup" => cs.lookup(TableId(op["table"].as_u64().unwrap() as usize), &lcs(&op["tuple"]))?,
                "lookup_value" => {
                    let v = if prover { Some(op["v"].as_u64().unwrap()) } else { None };
                    cs.lookup_value(TableId(op["table"].as_u64().unwrap() as usize), v)?;
                }
                "reciprocal" => {
                    let mut r = cs.reciprocal(&widths(&op["widths"]))?;
                    for t in op["terms"].as_array().unwrap() {
                        r.add_weighted(lc(&t["num"]), lcs(&t["tuple"]));
                    }
                    for t in op["public"].as_array().unwrap() {
                        r.add_public(lc(&t["coeff"]), ints(&t["row"]));
                    }
                    cs.finish_reciprocal(r)?;
                }
                x => panic!("op {}", x),
            }
            Ok(())
        })();
        r.map_err(|e| (i, e))?;
    }
    Ok(())
}

fn prover_run<'a>(pc: &'a PedersenGens, t: &'a mut Transcript, program: &[Value], backend: Backend) -> (Prover<'a, &'a mut Transcript>, Vec<CompressedRistretto>, Result<(), (usize, R1CSError)>) {
    let mut p = Prover::new(pc, t);
    p.set_backend(backend);
    let mut V = Vec::new();
    let r = run(&mut p, program, true, &mut |cs, v, s| {
        let (c, x) = cs.commit(v, s);
        V.push(c);
        x
    });
    (p, V, r)
}

fn verifier_run<'a>(t: &'a mut Transcript, program: &[Value], V: &[CompressedRistretto], backend: Backend) -> (Verifier<&'a mut Transcript>, Result<(), (usize, R1CSError)>) {
    let mut v = Verifier::new(t);
    v.set_backend(backend);
    let mut it = V.iter();
    let r = run(&mut v, program, false, &mut |cs, _, _| cs.commit(*it.next().unwrap()));
    (v, r)
}

#[test]
fn builder_matches_reference_vectors() {
    let file: Value = serde_json::from_str(include_str!("../../tests/vectors/bppp/builder.json")).unwrap();
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(4096, 1);
    let mut proven = 0;
    for case in file["cases"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let program = case["program"].as_array().unwrap();
        let (mut t1, mut t2) = (Transcript::new(b"v"), Transcript::new(b"v"));
        let (mut p, V, pr) = prover_run(&pc, &mut t1, program, Backend::Bppp);
        let (mut v, vr) = verifier_run(&mut t2, program, &V, Backend::Bppp);
        if let Some(at) = case["error"].as_u64() {
            let at = at as usize;
            assert_eq!(at, program.len() - 1, "{}: the failing op is the last", name);
            for r in [pr, vr] {
                match r {
                    Err((i, R1CSError::GadgetError { .. })) => assert_eq!(i, at, "{}", name),
                    other => panic!("{}: expected a gadget error at op {}, got {:?}", name, at, other),
                }
            }
            continue;
        }
        pr.unwrap_or_else(|e| panic!("{}: prover {:?}", name, e));
        vr.unwrap_or_else(|e| panic!("{}: verifier {:?}", name, e));
        if case["prover_error"].as_bool().unwrap() {
            assert!(matches!(p.lower_builder_bppp(), Err(R1CSError::GadgetError { .. })), "{}", name);
            v.lower_builder_bppp().unwrap();
            continue;
        }
        let costs = &case["costs"];
        let want = Cost {
            bp_phase1: costs["bp_phase1"].as_u64().unwrap() as usize,
            bp_phase2: costs["bp_phase2"].as_u64().unwrap() as usize,
            bppp_gates: costs["bppp_gates"].as_u64().unwrap() as usize,
            bppp_lin: case["n_lin"].as_u64().unwrap() as usize,
        };
        assert_eq!(p.cost(), want, "{}: prover cost", name);
        assert_eq!(v.cost(), want, "{}: verifier cost", name);
        let c = testutil::recip_circuit(case);
        let w = testutil::recip_witness(case);
        let cv = v.lower_builder_bppp().unwrap();
        assert_eq!(cv, c, "{}: verifier's circuit", name);
        let (cp, wp) = p.lower_builder_bppp().unwrap();
        assert_eq!(cp, c, "{}: prover's circuit", name);
        assert!(
            wp.w_d == w.w_d && wp.w_l == w.w_l && wp.w_r == w.w_r && wp.w_o == w.w_o && wp.v == w.v && wp.s == w.s,
            "{}: witness",
            name
        );
        testutil::run_recip_case(case, &c, &w);

        // Real proofs through the public API, both backends.
        let satisfied = case["satisfied"].as_bool().unwrap();
        for backend in [Backend::Bp, Backend::Bppp] {
            let (mut t1, mut t2) = (Transcript::new(b"real"), Transcript::new(b"real"));
            let (p, V, _) = prover_run(&pc, &mut t1, program, backend);
            let proof = p.prove_with_rng(&bp, &mut ChaCha20Rng::seed_from_u64(9));
            let verdict = proof.map(|proof| {
                let (v, _) = verifier_run(&mut t2, program, &V, backend);
                v.verify(&proof, &pc, &bp).is_ok()
            });
            assert_eq!(verdict.unwrap_or(false), satisfied, "{}: {:?} proof", name, backend);
        }
        proven += 1;
    }
    assert!(proven >= 10, "too few proven cases");
}

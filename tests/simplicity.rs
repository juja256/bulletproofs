//! The Simplicity verifier of an R1CS circuit (BP++ backend, secp256k1, SHA-256 transcript):
//! honest proofs run as a node would run them; tampered proofs, other transactions, other
//! transcripts are rejected.

#![cfg(feature = "simplicity")]
#![allow(non_snake_case)]

use bulletproofs::curve::{Curve, Secp256k1};
use bulletproofs::r1cs::{lc, Backend, CircuitBuilder, ConstraintSystem, Prover, R1CSProof, RandomizableConstraintSystem, RandomizedConstraintSystem, Variable, Verifier};
use bulletproofs::secp256k1::{BulletproofGens, PedersenGens, Scalar};
use bulletproofs::simplicity::{dummy_env, dummy_env_with_output, sighash_of, CompileTranscript, SimplicityVerifier, SIGHASH_LABEL};
use bulletproofs::{Sha256Transcript, TranscriptBackend, TranscriptRef};
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

type Compressed = <Secp256k1 as Curve>::Compressed;

fn gens() -> (PedersenGens, BulletproofGens) {
    (PedersenGens::for_curve(), BulletproofGens::for_curve(64, 1))
}

/// `x · y = 15` with committed `x`, `y`.
fn product<CS: ConstraintSystem<Scalar>>(cs: &mut CS, x: Variable, y: Variable) {
    let (_, _, o) = cs.multiply(lc(x), lc(y));
    cs.constrain(lc(o) - Scalar::from(15u64));
}

fn prove_with<T: TranscriptRef>(t: T, backend: Backend, seed: u64) -> (R1CSProof<Secp256k1>, Vec<Compressed>) {
    let (pc, bp) = gens();
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut p = Prover::new(&pc, t);
    p.set_backend(backend);
    let r = |rng: &mut ChaCha20Rng| <Scalar as bulletproofs::curve::ff::Field>::random(rng);
    let (cx, x) = p.commit(Scalar::from(3u64), r(&mut rng));
    let (cy, y) = p.commit(Scalar::from(5u64), r(&mut rng));
    product(&mut p, x, y);
    (p.prove_with_rng(&bp, &mut rng).unwrap(), vec![cx, cy])
}

/// A proof bound to `sighash`.
fn prove(sighash: [u8; 32], seed: u64) -> (R1CSProof<Secp256k1>, Vec<Compressed>) {
    let mut t = Sha256Transcript::new(b"test");
    t.append_message(SIGHASH_LABEL, &sighash);
    prove_with(&mut t, Backend::Bppp, seed)
}

fn compile_with(V: &[Compressed], backend: Backend, sighash: bool, randomized: bool) -> Result<SimplicityVerifier, bulletproofs::r1cs::R1CSError> {
    let (pc, bp) = gens();
    let mut ct = CompileTranscript::new(b"test");
    if sighash {
        ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
    }
    let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
    v.set_backend(backend);
    let x = v.commit(V[0]);
    let y = v.commit(V[1]);
    product(&mut v, x, y);
    if randomized {
        v.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"z");
            let (_, _, o) = cs.multiply(lc(x) - z, lc(y));
            cs.constrain(lc(o) - lc(o));
            Ok(())
        })
        .unwrap();
    }
    v.compile_to_simplicity(&pc, &bp)
}

fn compile(V: &[Compressed]) -> SimplicityVerifier {
    compile_with(V, Backend::Bppp, true, false).unwrap()
}

#[test]
fn honest_proof_verifies_as_a_node() {
    let env = dummy_env();
    let (proof, V) = prove(sighash_of(&env), 1);
    let sv = compile(&V);
    let w = sv.witness(&proof).unwrap();
    let r = sv.execute(&w, &env).unwrap();
    println!("x·y = 15: cost {} mWU of {} (program {} B, witness {} B, cells {}), {:?}", r.cost_mwu, r.budget_mwu, r.program_bytes, r.witness_bytes, r.cells, sv.stats());
    assert!(r.cost_mwu <= r.budget_mwu);
    assert!(r.cells <= 5_242_880);
    assert_eq!(r.cmr, sv.cmr());
}

#[test]
fn another_transaction_is_rejected() {
    let (proof, V) = prove(sighash_of(&dummy_env()), 2);
    let sv = compile(&V);
    let w = sv.witness(&proof).unwrap();
    assert!(sv.execute(&w, &dummy_env_with_output(7)).is_err());
}

#[test]
fn tampered_proofs_are_rejected() {
    let env = dummy_env();
    let (proof, V) = prove(sighash_of(&env), 3);
    let sv = compile(&V);
    let bytes = proof.to_bytes();
    // the BP++ encoding: a tag and the dimensions, then C_L, C_R, C_O, C_S, the rounds' points
    // and the final scalars; flip a bit in every 33-byte point and in the first scalar
    let n_points = sv.stats().witness_points;
    let body = bytes.len() - (33 * n_points + 32 * sv.stats().witness_scalars);
    let mut positions: Vec<usize> = (0..n_points).map(|i| body + 33 * i + 20).collect();
    positions.push(body + 33 * n_points + 31);
    for pos in positions {
        let mut b = bytes.clone();
        b[pos] ^= 1;
        let rejected = match R1CSProof::<Secp256k1>::from_bytes(&b) {
            Err(_) => true,
            Ok(p) => match sv.witness(&p) {
                Err(_) => true,
                Ok(w) => sv.execute(&w, &env).is_err(),
            },
        };
        assert!(rejected, "a proof with byte {} flipped verified", pos);
    }
}

#[test]
fn merlin_proof_is_rejected() {
    let env = dummy_env();
    let mut m = merlin::Transcript::new(b"test");
    m.append_message(SIGHASH_LABEL, &sighash_of(&env));
    let (proof, V) = prove_with(&mut m, Backend::Bppp, 4);
    let sv = compile(&V);
    let w = sv.witness(&proof).unwrap();
    assert!(sv.execute(&w, &env).is_err());
}

#[test]
fn compile_errors() {
    let (_, V) = prove(sighash_of(&dummy_env()), 5);
    assert!(compile_with(&V, Backend::Bp, true, false).is_err());
    assert!(compile_with(&V, Backend::Bppp, false, false).is_err());
    assert!(compile_with(&V, Backend::Bppp, true, true).is_err());
}

#[test]
fn program_is_deterministic() {
    let (_, V) = prove(sighash_of(&dummy_env()), 6);
    let (a, b) = (compile(&V), compile(&V));
    assert_eq!(a.to_text(), b.to_text());
    assert_eq!(a.cmr(), b.cmr());
}

/// A table lookup and a witness variable of the circuit builder (the reciprocal form has poles).
fn gadgets<CS: CircuitBuilder<Scalar>>(cs: &mut CS, x: Variable, y: Variable, prover: bool) {
    product(cs, x, y);
    let t = cs.table((0..16u64).map(|v| vec![v]).collect()).unwrap();
    let l = cs.lookup_value(t, if prover { Some(3) } else { None }).unwrap();
    cs.constrain(lc(l) - lc(x));
    let w = cs.witness(if prover { Some(Scalar::from(7u64)) } else { None }).unwrap();
    cs.constrain_product(lc(w), lc(y), lc(Variable::One()) * Scalar::from(35u64)).unwrap();
}

#[test]
fn circuit_builder_gadgets_verify() {
    let env = dummy_env();
    let (pc, bp) = gens();
    let mut rng = ChaCha20Rng::seed_from_u64(7);
    let mut t = Sha256Transcript::new(b"gadgets");
    t.append_message(SIGHASH_LABEL, &sighash_of(&env));
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let r = |rng: &mut ChaCha20Rng| <Scalar as bulletproofs::curve::ff::Field>::random(rng);
    let (cx, x) = p.commit(Scalar::from(3u64), r(&mut rng));
    let (cy, y) = p.commit(Scalar::from(5u64), r(&mut rng));
    gadgets(&mut p, x, y, true);
    let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
    let mut ct = CompileTranscript::new(b"gadgets");
    ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
    let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
    v.set_backend(Backend::Bppp);
    let (x, y) = (v.commit(cx), v.commit(cy));
    gadgets(&mut v, x, y, false);
    let sv = v.compile_to_simplicity(&pc, &bp).unwrap();
    let w = sv.witness(&proof).unwrap();
    match sv.execute(&w, &env) {
        Ok(r) => println!("gadgets: cost {} mWU of {}, cells {}", r.cost_mwu, r.budget_mwu, r.cells),
        Err(e) => panic!("{:?}", e),
    }
    assert!(sv.execute(&w, &dummy_env_with_output(7)).is_err());
}

/// `n` multiplications `v_{i+1} = v_i · x` from a committed `x`, the last value fixed.
fn chain<CS: ConstraintSystem<Scalar>>(cs: &mut CS, x: Variable, n: usize) {
    let mut last = Scalar::from(3u64);
    let mut v = lc(x);
    for _ in 0..n {
        let (_, _, o) = cs.multiply(v, lc(x));
        v = lc(o);
        last *= Scalar::from(3u64);
    }
    cs.constrain(v - last);
}

fn chain_proof_and_verifier(n: usize, env: &bulletproofs::simplicity::Env) -> (R1CSProof<Secp256k1>, SimplicityVerifier) {
    let pc = PedersenGens::for_curve();
    let bp = BulletproofGens::for_curve(2 * n + 64, 1);
    let mut rng = ChaCha20Rng::seed_from_u64(n as u64);
    let mut t = Sha256Transcript::new(b"chain");
    t.append_message(SIGHASH_LABEL, &sighash_of(env));
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let (cx, x) = p.commit(Scalar::from(3u64), <Scalar as bulletproofs::curve::ff::Field>::random(&mut rng));
    chain(&mut p, x, n);
    let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
    let mut ct = CompileTranscript::new(b"chain");
    ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
    let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
    v.set_backend(Backend::Bppp);
    let x = v.commit(cx);
    chain(&mut v, x, n);
    (proof, v.compile_to_simplicity(&pc, &bp).unwrap())
}

/// Chains of 2, 4 and 8 gates verify within the budget and the cell limit; a proof of 2 gates
/// does not fit the 4-gate program.
#[test]
fn chains_verify() {
    let env = dummy_env();
    let mut built = Vec::new();
    for n in [2, 4, 8] {
        let (p, v) = chain_proof_and_verifier(n, &env);
        let r = v.execute(&v.witness(&p).unwrap(), &env).unwrap();
        println!("chain {}: tape {} msm {} cost {} mWU of {}, cells {}", n, v.stats().tape_ops, v.stats().msm_terms, r.cost_mwu, r.budget_mwu, r.cells);
        assert!(r.cells <= bulletproofs::simplicity::MAX_CELLS);
        built.push((p, v));
    }
    assert!(built[1].1.witness(&built[0].0).is_err());
}

/// `x · y = c`.
fn product_eq<CS: ConstraintSystem<Scalar>>(cs: &mut CS, x: Variable, y: Variable, c: u64) {
    let (_, _, o) = cs.multiply(lc(x), lc(y));
    cs.constrain(lc(o) - Scalar::from(c));
}

fn prove_eq(env: &bulletproofs::simplicity::Env, x: u64, y: u64, c: u64, blind_x: Option<Scalar>, seed: u64) -> (R1CSProof<Secp256k1>, Vec<Compressed>) {
    let (pc, bp) = gens();
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut t = Sha256Transcript::new(b"test");
    t.append_message(SIGHASH_LABEL, &sighash_of(env));
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let r = |rng: &mut ChaCha20Rng| <Scalar as bulletproofs::curve::ff::Field>::random(rng);
    let bx = blind_x.unwrap_or_else(|| r(&mut rng));
    let (cx, xv) = p.commit(Scalar::from(x), bx);
    let (cy, yv) = p.commit(Scalar::from(y), r(&mut rng));
    product_eq(&mut p, xv, yv, c);
    (p.prove_with_rng(&bp, &mut rng).unwrap(), vec![cx, cy])
}

fn compile_eq(V: &[Compressed], c: u64) -> SimplicityVerifier {
    let (pc, bp) = gens();
    let mut ct = CompileTranscript::new(b"test");
    ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
    let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
    v.set_backend(Backend::Bppp);
    let (x, y) = (v.commit(V[0]), v.commit(V[1]));
    product_eq(&mut v, x, y, c);
    v.compile_to_simplicity(&pc, &bp).unwrap()
}

/// A commitment to zero with a zero blinding is the identity (a valid statement point):
/// the compiler handles it and the program verifies the proof.
#[test]
fn identity_commitment_compiles_and_verifies() {
    let env = dummy_env();
    let (proof, V) = prove_eq(&env, 0, 5, 0, Some(<Scalar as bulletproofs::curve::ff::Field>::ZERO), 8);
    assert_eq!(V[0], Compressed::default());
    let sv = compile_eq(&V, 0);
    sv.execute(&sv.witness(&proof).unwrap(), &env).unwrap();
}

/// A proof of another circuit with the same dimensions (`x · y = 16` against `x · y = 15`,
/// the same commitments' structure) is rejected by the program.
#[test]
fn proof_of_another_circuit_is_rejected() {
    let env = dummy_env();
    let (proof16, V16) = prove_eq(&env, 4, 4, 16, None, 9);
    let sv15 = compile_eq(&V16, 15);
    let w = sv15.witness(&proof16).unwrap();
    assert!(sv15.execute(&w, &env).is_err());
    let sv16 = compile_eq(&V16, 16);
    sv16.execute(&sv16.witness(&proof16).unwrap(), &env).unwrap();
}

/// Stage 2 is not worse than stage 1 (its measured cost and program size) on the same
/// circuits: `x · y = 15` and the chains of 2, 4 and 8 gates.
#[test]
fn new_backend_not_worse_than_stage1() {
    let env = dummy_env();
    let (proof, V) = prove(sighash_of(&env), 1);
    let sv = compile(&V);
    let r = sv.execute(&sv.witness(&proof).unwrap(), &env).unwrap();
    assert!(r.cost_mwu <= 8_412_334 && r.program_bytes <= 16_020, "x·y = 15: {} mWU, {} B", r.cost_mwu, r.program_bytes);
    for (n, cost, bytes) in [(2, 8_507_765u64, 15_922usize), (4, 13_437_957, 27_152), (8, 22_254_683, 42_004)] {
        let (p, v) = chain_proof_and_verifier(n, &env);
        let r = v.execute(&v.witness(&p).unwrap(), &env).unwrap();
        println!("chain {}: {} mWU (stage 1: {}), {} B (stage 1: {}), steps {}, live bits {}", n, r.cost_mwu, cost, r.program_bytes, bytes, v.stats().steps, v.stats().live_bits);
        assert!(r.cost_mwu <= cost && r.program_bytes <= bytes, "chain {}", n);
    }
}

/// Stage 3 is not worse than stage 2 (its measured cost and program size, 2026-10-21) on the
/// same circuits: `x · y = 15` and the chains of 2 to 64 gates.
#[test]
fn stage3_not_worse_than_stage2() {
    let env = dummy_env();
    let (proof, V) = prove(sighash_of(&env), 1);
    let sv = compile(&V);
    let r = sv.execute(&sv.witness(&proof).unwrap(), &env).unwrap();
    println!("x·y = 15: {} mWU (stage 2: 3134520), {} B (stage 2: 6102), data {} mWU", r.cost_mwu, r.program_bytes, r.data_mwu);
    assert!(r.cost_mwu <= 3_134_520 && r.program_bytes <= 6_102, "x·y = 15");
    for (n, cost, bytes) in [
        (2, 3_103_445u64, 6_156usize),
        (4, 4_051_373, 7_694),
        (8, 5_478_297, 9_694),
        (16, 9_675_434, 15_731),
        (32, 19_483_906, 26_412),
        (64, 50_551_736, 50_408),
    ] {
        let (p, v) = chain_proof_and_verifier(n, &env);
        let r = v.execute(&v.witness(&p).unwrap(), &env).unwrap();
        println!("chain {}: {} mWU (stage 2: {}), {} B (stage 2: {}), data {} mWU, steps {}", n, r.cost_mwu, cost, r.program_bytes, bytes, r.data_mwu, v.stats().steps);
        assert!(r.cost_mwu <= cost && r.program_bytes <= bytes, "chain {}", n);
    }
}

/// `lookups` lookups into a table of `rows` values (a range table, as bpvm's VM has): the
/// verifier inverts `rows` challenge-dependent values.
fn table_circuit<CS: CircuitBuilder<Scalar>>(cs: &mut CS, rows: u64, lookups: u64, prover: bool) {
    let t = cs.table((0..rows).map(|v| vec![v]).collect()).unwrap();
    for i in 0..lookups {
        cs.lookup_value(t, if prover { Some((i * 7) % rows) } else { None }).unwrap();
    }
}

/// The program of a table circuit, run on an honest proof.
fn table_program(rows: u64, lookups: u64, env: &bulletproofs::simplicity::Env) -> (SimplicityVerifier, Result<bulletproofs::simplicity::Report, bulletproofs::simplicity::ExecError>) {
    let pc = PedersenGens::for_curve();
    let bp = BulletproofGens::for_curve((4 * rows + 256) as usize, 1);
    let mut rng = ChaCha20Rng::seed_from_u64(rows);
    let mut t = Sha256Transcript::new(b"table");
    t.append_message(SIGHASH_LABEL, &sighash_of(env));
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    table_circuit(&mut p, rows, lookups, true);
    let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
    let mut ct = CompileTranscript::new(b"table");
    ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
    let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
    v.set_backend(Backend::Bppp);
    table_circuit(&mut v, rows, lookups, false);
    let sv = v.compile_to_simplicity(&pc, &bp).unwrap();
    let r = sv.execute(&sv.witness(&proof).unwrap(), env);
    (sv, r)
}

/// The input's weight in mWU, padded if the cost needs it: the larger of the budget and the
/// cost (`Budget` is reported only after every check has passed).
fn weight(r: Result<bulletproofs::simplicity::Report, bulletproofs::simplicity::ExecError>) -> u64 {
    match r {
        Ok(r) => r.budget_mwu.max(r.cost_mwu),
        Err(bulletproofs::simplicity::ExecError::Budget { cost_mwu, .. }) => cost_mwu,
        Err(e) => panic!("rejected: {:?}", e),
    }
}

/// The program grows linearly with the table: 4× the rows, at most 5× the weight (stage 3 gave
/// 8.3× the bytes and 8.1× the cost: products of many factors were expanded from scratch).
#[test]
fn table_program_grows_linearly() {
    let env = dummy_env();
    let (a, b) = (weight(table_program(64, 8, &env).1), weight(table_program(256, 8, &env).1));
    println!("table 64: {} mWU, table 256: {} mWU (weights)", a, b);
    assert!(b <= 5 * a, "the weight grows {:.1}×", b as f64 / a as f64);
}

/// Stage 4 is not heavier than stage 3 (the input's weight, padded if needed: stage 3's
/// budgets, every one above its cost, 2026-10-21) on the chains of 2 to 64 gates.
#[test]
fn stage4_not_heavier_than_stage3() {
    let env = dummy_env();
    for (n, stage3) in [(2, 5_420_000u64), (4, 6_315_000), (8, 7_983_000), (16, 11_303_000), (32, 18_418_000), (64, 32_243_000)] {
        let (p, v) = chain_proof_and_verifier(n, &env);
        let w = weight(v.execute(&v.witness(&p).unwrap(), &env));
        println!("chain {}: {} mWU (stage 3: {})", n, w, stage3);
        assert!(w <= stage3, "chain {}", n);
    }
}

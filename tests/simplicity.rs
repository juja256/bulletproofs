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

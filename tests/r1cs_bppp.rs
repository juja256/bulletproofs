//! The R1CS front end on the BP++ backend (spec §6): the same gadgets proven with both
//! backends, backend mismatches, randomized constraints, malformed proofs.

#![allow(non_snake_case)]

use std::convert::TryInto;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

/// The statement: committed `x, y, z` with `x * y = z`, and a committed `v` with an `n`-bit
/// decomposition (`b (1 - b) = 0`, `sum 2^i b_i = v`), plus one lone `allocate()` that leaves a
/// pending multiplier, constrained to 3.
fn gadget<CS: ConstraintSystem>(cs: &mut CS, vars: &[Variable], bits: Option<u64>, n: usize) -> Result<(), R1CSError> {
    let (_, _, o) = cs.multiply(vars[0].into(), vars[1].into());
    cs.constrain(o - vars[2]);
    let mut sum = LinearCombination::default();
    let mut pow = Scalar::ONE;
    for i in 0..n {
        let bit = bits.map(|v| Scalar::from((v >> i) & 1));
        let (a, b, o) = cs.allocate_multiplier(bit.map(|b| (Scalar::ONE - b, b)))?;
        cs.constrain(o.into());
        cs.constrain(a + b - Scalar::ONE);
        sum = sum + b * pow;
        pow += pow;
    }
    cs.constrain(sum - vars[3]);
    let lone = cs.allocate(bits.map(|_| Scalar::from(3u64)))?;
    cs.constrain(lone - Scalar::from(3u64));
    Ok(())
}

fn prove(backend: Backend, values: [u64; 4], n: usize, pc: &PedersenGens, bp: &BulletproofGens) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let mut rng = ChaCha20Rng::seed_from_u64(values[3]);
    let mut t = Transcript::new(b"r1cs-bppp");
    let mut prover = Prover::new(pc, &mut t);
    prover.set_backend(backend);
    let (V, vars): (Vec<_>, Vec<_>) = values.iter().map(|v| prover.commit(Scalar::from(*v), Scalar::from(v + 11))).unzip();
    gadget(&mut prover, &vars, Some(values[3]), n)?;
    let proof = prover.prove_with_rng(bp, &mut rng)?;
    Ok((proof, V))
}

fn verify(backend: Backend, proof: &R1CSProof, V: &[CompressedRistretto], n: usize, pc: &PedersenGens, bp: &BulletproofGens) -> Result<(), R1CSError> {
    let mut t = Transcript::new(b"r1cs-bppp");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(backend);
    let vars: Vec<Variable> = V.iter().map(|v| verifier.commit(*v)).collect();
    gadget(&mut verifier, &vars, None, n)?;
    verifier.verify(proof, pc, bp)
}

#[test]
fn same_gadget_both_backends() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(128, 1);
    for &(n, v) in &[(8usize, 200u64), (32, 0xdead_beef), (60, (1 << 60) - 1)] {
        let values = [6, 7, 42, v];
        for &backend in &[Backend::Bp, Backend::Bppp] {
            let (proof, V) = prove(backend, values, n, &pc, &bp).unwrap();
            let parsed = R1CSProof::from_bytes(&proof.to_bytes()).unwrap();
            assert_eq!(parsed.to_bytes(), proof.to_bytes());
            assert_eq!(proof.serialized_size(), proof.to_bytes().len());
            verify(backend, &parsed, &V, n, &pc, &bp).unwrap();
            let other = if backend == Backend::Bp { Backend::Bppp } else { Backend::Bp };
            assert!(verify(other, &proof, &V, n, &pc, &bp).is_err(), "proof of {:?} accepted by {:?}", backend, other);
            // another statement (one more bit) is rejected
            assert!(verify(backend, &proof, &V, n + 1, &pc, &bp).is_err());
        }
        let bp_size = prove(Backend::Bp, values, n, &pc, &bp).unwrap().0.serialized_size();
        let bppp_size = prove(Backend::Bppp, values, n, &pc, &bp).unwrap().0.serialized_size();
        assert!(bppp_size < bp_size, "n = {}: BP++ {} B vs BP {} B", n, bppp_size, bp_size);
    }
}

/// An unsatisfied witness never yields a verifying proof. The BP++ prover recomputes the
/// constants from its witness, so a linear violation gives a proof of another circuit (another
/// digest), which the verifier rejects.
#[test]
fn unsatisfied_witness_does_not_verify() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    // 6 * 7 != 41; 300 does not fit 8 bits (its decomposition mod 256 does not sum to 300)
    for values in [[6u64, 7, 41, 5], [6, 7, 42, 300]] {
        if let Ok((proof, V)) = prove(Backend::Bppp, values, 8, &pc, &bp) {
            assert!(verify(Backend::Bppp, &proof, &V, 8, &pc, &bp).is_err(), "{:?}", values);
        }
    }
}

/// Several constant terms in one constraint add up (`(x + 1) + 2 - c = 0` with `c = x + 3`).
#[test]
fn several_constants_in_one_constraint() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    let mut t = Transcript::new(b"consts");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (vx, x) = prover.commit(Scalar::from(5u64), Scalar::from(1u64));
    let (vc, c) = prover.commit(Scalar::from(8u64), Scalar::from(2u64));
    prover.constrain((x + Scalar::ONE) + Scalar::from(2u64) - c);
    let proof = prover.prove(&bp).unwrap();
    let check = |offset: u64| {
        let mut t = Transcript::new(b"consts");
        let mut verifier = Verifier::new(&mut t);
        verifier.set_backend(Backend::Bppp);
        let (x, c) = (verifier.commit(vx), verifier.commit(vc));
        verifier.constrain((x + Scalar::ONE) + Scalar::from(2u64 + offset) - c);
        verifier.verify(&proof, &pc, &bp)
    };
    check(0).unwrap();
    assert!(check(1).is_err());
}

/// A variable that the constraint system never allocated is a gadget error on BP++ (it would
/// otherwise alias another column).
#[test]
fn foreign_variables_are_gadget_errors() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    for var in [Variable::MultiplierLeft(1), Variable::MultiplierOutput(5), Variable::Committed(1)] {
        let mut t = Transcript::new(b"foreign");
        let mut prover = Prover::new(&pc, &mut t);
        prover.set_backend(Backend::Bppp);
        let (_, x) = prover.commit(Scalar::from(5u64), Scalar::from(1u64));
        let (_, _, o) = prover.allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(3u64)))).unwrap();
        prover.constrain(o - Scalar::from(6u64) + x - Scalar::from(5u64) + var);
        match prover.prove(&bp) {
            Err(R1CSError::GadgetError { .. }) => {}
            other => panic!("{:?}: expected a gadget error, got {:?}", var, other.map(|_| ())),
        }
    }
}

#[test]
fn no_commitments_and_no_multipliers() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    // no commitments: a product of allocated values
    let run = |backend: Backend| {
        let mut t = Transcript::new(b"k0");
        let mut prover = Prover::new(&pc, &mut t);
        prover.set_backend(backend);
        let (_, _, o) = prover.allocate_multiplier(Some((Scalar::from(3u64), Scalar::from(5u64)))).unwrap();
        prover.constrain(o - Scalar::from(15u64));
        let proof = prover.prove(&bp).unwrap();
        let mut t = Transcript::new(b"k0");
        let mut verifier = Verifier::new(&mut t);
        verifier.set_backend(backend);
        let (_, _, o) = verifier.allocate_multiplier(None).unwrap();
        verifier.constrain(o - Scalar::from(15u64));
        verifier.verify(&proof, &pc, &bp)
    };
    run(Backend::Bp).unwrap();
    run(Backend::Bppp).unwrap();
    // no multipliers: two committed values that are equal (one dummy gate on BP++)
    let mut t = Transcript::new(b"m0");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (a, x) = prover.commit(Scalar::from(9u64), Scalar::from(1u64));
    let (b, y) = prover.commit(Scalar::from(9u64), Scalar::from(2u64));
    prover.constrain(x - y);
    let proof = prover.prove(&bp).unwrap();
    let mut t = Transcript::new(b"m0");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(Backend::Bppp);
    let (x, y) = (verifier.commit(a), verifier.commit(b));
    verifier.constrain(x - y);
    verifier.verify(&proof, &pc, &bp).unwrap();
}

/// Randomized constraints cannot run on BP++ (the challenge would sit between `C_O` and
/// `C_R`, where right wires are unbound); both sides return a gadget error.
#[test]
fn randomized_constraints_need_bp() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    let mut t = Transcript::new(b"rand");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (_, x) = prover.commit(Scalar::from(4u64), Scalar::from(1u64));
    prover
        .specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"z");
            let (l, _, o) = cs.multiply(x - z, x - z);
            cs.constrain(o - l * Scalar::from(2u64) + l);
            Ok(())
        })
        .unwrap();
    match prover.prove(&bp) {
        Err(R1CSError::GadgetError { .. }) => {}
        other => panic!("expected a gadget error, got {:?}", other.map(|_| ())),
    }
    // the verifier refuses too: otherwise a proof of the circuit without the randomized part
    // would pass for a statement that also has it (found in review)
    let mut t = Transcript::new(b"rand");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (vx, _) = prover.commit(Scalar::from(4u64), Scalar::from(1u64));
    let proof = prover.prove(&bp).unwrap();
    let mut t = Transcript::new(b"rand");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(Backend::Bppp);
    let x = verifier.commit(vx);
    verifier
        .specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"z");
            cs.constrain(x - z);
            Ok(())
        })
        .unwrap();
    match verifier.verify(&proof, &pc, &bp) {
        Err(R1CSError::GadgetError { .. }) => {}
        other => panic!("expected a gadget error, got {:?}", other),
    }
}

#[test]
fn malformed_bppp_proofs_are_rejected() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    let (proof, V) = prove(Backend::Bppp, [6, 7, 42, 200], 8, &pc, &bp).unwrap();
    let bytes = proof.to_bytes();
    assert_eq!(bytes[0], 4, "BP++ tag");
    assert!(R1CSProof::from_bytes(&bytes[..bytes.len() - 1]).is_err());
    assert!(R1CSProof::from_bytes(&bytes[..10]).is_err());
    // wrong dimensions in the header: parses (or not) but never verifies
    let mut wrong = bytes.clone();
    wrong[1] ^= 1;
    if let Ok(p) = R1CSProof::from_bytes(&wrong) {
        assert!(verify(Backend::Bppp, &p, &V, 8, &pc, &bp).is_err());
    }
    let mut tampered = bytes.clone();
    let last = tampered.len() - 40;
    tampered[last] ^= 1;
    if let Ok(p) = R1CSProof::from_bytes(&tampered) {
        assert!(verify(Backend::Bppp, &p, &V, 8, &pc, &bp).is_err());
    }
    // a header with other dimensions that still parse (same norm-argument shape) must not
    // verify: the encoding of a proof is unique
    let n_m = u64::from_le_bytes(bytes[1..9].try_into().unwrap());
    let mut parsed_any = false;
    for other in [n_m - 1, n_m + 1, n_m + 2, n_m + 3] {
        let mut h = bytes.clone();
        h[1..9].copy_from_slice(&other.to_le_bytes());
        if let Ok(p) = R1CSProof::from_bytes(&h) {
            parsed_any = true;
            assert!(verify(Backend::Bppp, &p, &V, 8, &pc, &bp).is_err(), "header n_m = {}", other);
        }
    }
    assert!(parsed_any, "no neighbouring n_m with the same shape; pick other sizes");
    // too few generators: an error, not a panic
    let small = BulletproofGens::new(4, 1);
    assert!(prove(Backend::Bppp, [6, 7, 42, 200], 8, &pc, &small).is_err());
}

/// Option B (spec §6): one BP++ encoding for every constraint system — the byte 4, `N'_m` and
/// `N_lin`, then the reciprocal form proof; the old tags 2 and 3 are format errors. A plain
/// R1CS has `N'_m = max(1, n)` and `N_lin = k`.
#[test]
fn one_encoding_for_every_constraint_system() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    let (proof, V) = prove(Backend::Bppp, [6, 7, 42, 200], 8, &pc, &bp).unwrap();
    let bytes = proof.to_bytes();
    let u = |i: usize| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap());
    // n = 1 (multiply) + 8 (bits) + 1 (allocate), k = 4
    assert_eq!((bytes[0], u(1), u(9)), (4, 10, 4));
    verify(Backend::Bppp, &R1CSProof::from_bytes(&bytes).unwrap(), &V, 8, &pc, &bp).unwrap();
    // the tags of the BP++ encodings before option B (2: §3 proof of a plain R1CS with the same
    // header and body layout, 3: builder) are format errors, not proofs that fail later
    for old in [2u8, 3] {
        let mut x = bytes.clone();
        x[0] = old;
        assert!(matches!(R1CSProof::from_bytes(&x), Err(R1CSError::FormatError)), "tag {}", old);
    }
    // the same statement written with a builder operation (a witness tied to x) is the same
    // kind of proof
    let mut t = Transcript::new(b"one");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let (vx, x) = p.commit(Scalar::from(4u64), Scalar::from(1u64));
    let w = p.witness(Some(Scalar::from(4u64))).unwrap();
    p.constrain(w - x);
    let b = p.prove(&bp).unwrap().to_bytes();
    assert_eq!(b[0], 4);
    let mut t = Transcript::new(b"one");
    let mut v = Verifier::new(&mut t);
    v.set_backend(Backend::Bppp);
    let x = v.commit(vx);
    let w = v.witness(None).unwrap();
    v.constrain(w - x);
    v.verify(&R1CSProof::from_bytes(&b).unwrap(), &pc, &bp).unwrap();
}

/// Corner cases of the plain lowering (review of option B): an empty constraint system (one
/// padding gate, no inputs) proves and verifies on BP++ and is rejected by the other backend; a
/// builder `Witness` in a plain constraint is a `GadgetError` on both sides.
#[test]
fn plain_corner_cases() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    let mut t = Transcript::new(b"empty");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let proof = p.prove(&bp).unwrap();
    let bytes = proof.to_bytes();
    assert_eq!((bytes[0], u64::from_le_bytes(bytes[1..9].try_into().unwrap()), u64::from_le_bytes(bytes[9..17].try_into().unwrap())), (4, 1, 0));
    for backend in [Backend::Bppp, Backend::Bp] {
        let mut t = Transcript::new(b"empty");
        let mut v = Verifier::new(&mut t);
        v.set_backend(backend);
        assert_eq!(v.verify(&proof, &pc, &bp).is_ok(), backend == Backend::Bppp, "{:?}", backend);
    }
    let mut t = Transcript::new(b"w");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(Backend::Bppp);
    let (V, x) = p.commit(Scalar::from(1u64), Scalar::from(2u64));
    p.constrain(x - Variable::Witness(0));
    assert!(matches!(p.prove(&bp), Err(R1CSError::GadgetError { .. })));
    let mut t = Transcript::new(b"w");
    let mut v = Verifier::new(&mut t);
    v.set_backend(Backend::Bppp);
    let x = v.commit(V);
    v.constrain(x - Variable::Witness(0));
    assert!(matches!(v.verify(&proof, &pc, &bp), Err(R1CSError::GadgetError { .. })));
}

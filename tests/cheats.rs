//! The `cheats` feature: a prover that skips its own checks (lookups equal to no row,
//! unsatisfied circuits) must produce proofs that the verifier rejects, on both backends.
//! Downstream crates (bpvm) use it for soundness tests of whole circuits.

#![cfg(feature = "cheats")]

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use bulletproofs::curve::Ristretto;

type Lc = LinearCombination<Scalar>;

fn backends() -> Vec<Backend> {
    #[allow(unused_mut)]
    let mut b = vec![Backend::Bp];
    b.push(Backend::Bppp);
    b
}

/// What the gadget gets wrong.
#[derive(Clone, Copy, Debug)]
enum Fault {
    None,
    /// A byte lookup of 256.
    Lookup,
    /// A memory argument whose read differs from the write.
    Reciprocal,
    /// `x = 2 y` with `x = 2 y + 1`.
    Linear,
}

fn gadget<CS: ConstraintSystem<Scalar>>(cs: &mut CS, fault: Fault, prover: bool) -> Result<(), R1CSError> {
    let v = |x: u64| if prover { Some(Scalar::from(x)) } else { None };
    let byte = cs.table((0..256u64).map(|x| vec![x]).collect())?;
    let b = cs.witness(v(if matches!(fault, Fault::Lookup) { 256 } else { 17 }))?;
    cs.lookup(byte, &[b.into()])?;
    let arg = cs.reciprocal(2)?;
    let (a, w) = (cs.witness(v(3))?, cs.witness(v(5))?);
    let r = cs.witness(v(if matches!(fault, Fault::Reciprocal) { 6 } else { 5 }))?;
    arg.add(cs, &[a.into(), w.into()])?;
    arg.sub(cs, &[a.into(), r.into()])?;
    let y = cs.witness(v(4))?;
    let x = cs.witness(v(if matches!(fault, Fault::Linear) { 9 } else { 8 }))?;
    cs.constrain(Lc::from(x) - y * Scalar::from(2u64));
    let o = cs.multiply(b.into(), y.into()).unwrap();
    cs.constrain(o - Lc::from(b) * Scalar::from(4u64));
    Ok(())
}

fn prove(backend: Backend, fault: Fault) -> Result<R1CSProof<Ristretto>, R1CSError> {
    let pc = PedersenGens::default();
    let mut t = Transcript::new(b"cheats");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(backend);
    gadget(&mut p, fault, true)?;
    let cap = p.cost().gens_capacity(backend).max(16);
    p.prove(&BulletproofGens::new(cap.next_power_of_two(), 1))
}

fn verify(backend: Backend, proof: &R1CSProof<Ristretto>) -> Result<(), R1CSError> {
    let pc = PedersenGens::default();
    let mut t = Transcript::new(b"cheats");
    let mut v = Verifier::new(&mut t);
    v.set_backend(backend);
    gadget(&mut v, Fault::None, false)?;
    let cap = v.cost().gens_capacity(backend).max(16);
    v.verify(proof, &pc, &BulletproofGens::new(cap.next_power_of_two(), 1))
}

#[test]
fn honest_proofs_verify_and_name_their_backend() {
    for backend in backends() {
        let proof = prove(backend, Fault::None).unwrap();
        assert_eq!(proof.backend(), backend);
        let parsed = R1CSProof::from_bytes(&proof.to_bytes()).unwrap();
        assert_eq!(parsed.backend(), backend);
        verify(backend, &parsed).unwrap();
    }
}

#[test]
fn honest_prover_refuses_a_lookup_equal_to_no_row() {
    cheats::set_unchecked_prover(false);
    for backend in backends() {
        assert!(prove(backend, Fault::Lookup).is_err(), "{:?}", backend);
    }
    // BP++ also refuses an unsatisfied reciprocal argument (BP proves it, as upstream proves
    // violated constraints). A violated linear constraint is proven by both: the constants are
    // derived from the witness, so the proof is of another circuit and fails verification.
    assert!(prove(Backend::Bppp, Fault::Reciprocal).is_err());
}

#[test]
fn unchecked_prover_proofs_are_rejected() {
    for backend in backends() {
        for fault in [Fault::Lookup, Fault::Reciprocal, Fault::Linear] {
            cheats::set_unchecked_prover(true);
            let proof = prove(backend, fault);
            cheats::set_unchecked_prover(false);
            let proof = proof.unwrap_or_else(|e| panic!("{:?} {:?}: the unchecked prover refused: {:?}", backend, fault, e));
            assert!(verify(backend, &proof).is_err(), "{:?} {:?}: a cheating proof verified", backend, fault);
        }
    }
}

#[test]
fn the_flag_is_per_thread_and_resets() {
    cheats::set_unchecked_prover(true);
    let other = std::thread::spawn(|| backends().into_iter().all(|b| prove(b, Fault::Lookup).is_err()));
    assert!(other.join().unwrap(), "another thread saw the flag");
    cheats::set_unchecked_prover(false);
    for backend in backends() {
        assert!(prove(backend, Fault::Lookup).is_err());
    }
}

#[test]
fn the_scoped_flag_resets_even_after_a_panic() {
    for backend in backends() {
        let proof = cheats::with_unchecked_prover(|| prove(backend, Fault::Lookup)).unwrap();
        assert!(verify(backend, &proof).is_err());
        assert!(prove(backend, Fault::Lookup).is_err(), "reset after the closure");
        let r = std::panic::catch_unwind(|| cheats::with_unchecked_prover(|| panic!("inside")));
        assert!(r.is_err());
        assert!(prove(backend, Fault::Lookup).is_err(), "reset after a panic");
    }
}

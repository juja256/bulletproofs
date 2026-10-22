//! The shape of the public API: one constructor per type, generic over the curve, with no
//! default type parameters. This file compiles only against that API.

use bulletproofs::curve::{Curve, Ristretto, Secp256k1};
use bulletproofs::r1cs::{Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens, Sha256Transcript};
use merlin::Transcript;

fn constructors<C: Curve>() {
    let pc = PedersenGens::<C>::default();
    let _bp = BulletproofGens::<C>::new(64, 1);
    let mut t = Transcript::new(b"api");
    let _p = Prover::new(&pc, &mut t);
    let mut t = Sha256Transcript::new(b"api");
    let _v = Verifier::<_, C>::new(&mut t);
}

#[test]
fn one_constructor_per_type() {
    constructors::<Ristretto>();
    constructors::<Secp256k1>();
}

use bulletproofs::curve::Field;
use bulletproofs::r1cs::{Backend, ConstraintSystem, LinearCombination, R1CSError, Variable};

/// `c = a^3` for `a` in a table, with every kind of operation and one trait bound.
fn cube<F: Field, CS: ConstraintSystem<F>>(cs: &mut CS, x: Option<u64>) -> Result<Variable, R1CSError> {
    let a = cs.witness(x.map(F::from))?;
    let b = cs.multiply(a.into(), a.into())?;
    let c = cs.witness(x.map(|x| F::from(x * x * x)))?;
    cs.constrain_product(a.into(), b.into(), c.into())?;
    let t = cs.table(vec![vec![0], vec![1], vec![2]])?;
    let y = cs.lookup_value(t, x)?;
    cs.constrain(LinearCombination::from(y) - LinearCombination::from(a));
    let r = cs.reciprocal(1)?;
    r.add(cs, &[a.into()])?;
    r.sub(cs, &[y.into()])?;
    assert!(cs.cost().gates(Backend::Bppp) > 0);
    Ok(c)
}

fn prove_cube<C: Curve>(backend: Backend) {
    let pc = PedersenGens::<C>::default();
    let bp = BulletproofGens::<C>::new(64, 1);
    let mut t = Transcript::new(b"cube");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(backend);
    let c = cube(&mut p, Some(2)).unwrap();
    p.constrain(LinearCombination::from(c) - LinearCombination::from(C::Scalar::from(8u64)));
    let proof = p.prove(&bp).unwrap();
    let mut t = Transcript::new(b"cube");
    let mut v = Verifier::<_, C>::new(&mut t);
    v.set_backend(backend);
    let c = cube(&mut v, None).unwrap();
    v.constrain(LinearCombination::from(c) - LinearCombination::from(C::Scalar::from(8u64)));
    v.verify(&proof, &pc, &bp).unwrap();
}

#[test]
fn one_constraint_system_trait() {
    for backend in [Backend::Bp, Backend::Bppp] {
        prove_cube::<Ristretto>(backend);
        prove_cube::<Secp256k1>(backend);
    }
}

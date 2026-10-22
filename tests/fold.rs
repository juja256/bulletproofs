//! Free witnesses alone in a product become the product's wires: a witness costs nothing of
//! its own when it is the left or right input of a product (`multiply` or `constrain_product`),
//! and stays constrained everywhere else it is used.

use bulletproofs::curve::Ristretto;
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

type Lc = LinearCombination<Scalar>;

const BACKENDS: [Backend; 2] = [Backend::Bp, Backend::Bppp];

fn val(prover: bool, x: u64) -> Option<Scalar> {
    prover.then(|| Scalar::from(x))
}

/// Prove with `gadget` (given `true`) and verify with it (given `false`); `cost` is the
/// prover's.
fn run<G>(backend: Backend, gadget: G) -> (Result<(), R1CSError>, Cost)
where
    G: Fn(&mut dyn ConstraintSystem<Scalar>, bool) -> Result<(), R1CSError>,
{
    let pc = PedersenGens::<Ristretto>::default();
    let mut t = Transcript::new(b"fold");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(backend);
    gadget(&mut p, true).unwrap();
    let cost = p.cost();
    let bp = BulletproofGens::new(cost.gens_capacity(backend).max(16), 1);
    let proof = match p.prove(&bp) {
        Ok(proof) => proof,
        Err(e) => return (Err(e), cost),
    };
    let mut t = Transcript::new(b"fold");
    let mut v = Verifier::<_, Ristretto>::new(&mut t);
    v.set_backend(backend);
    gadget(&mut v, false).unwrap();
    assert_eq!(v.cost(), cost, "the verifier computes the same cost");
    (v.verify(&proof, &pc, &bp), cost)
}

/// `b (1 - b) = 0`: a bit, one multiplier and no linear slot, as `allocate_multiplier` cost.
#[test]
fn boolean_gadget_costs_one_multiplier() {
    for backend in BACKENDS {
        for bit in [0, 1] {
            let (res, cost) = run(backend, |cs, prover| {
                let b = cs.witness(val(prover, bit))?;
                cs.constrain_product(b.into(), Lc::from(Scalar::ONE) - b, Lc::default())
            });
            res.unwrap();
            assert_eq!((cost.gates(Backend::Bp), cost.gates(Backend::Bppp), cost.linear(Backend::Bppp)), (1, 1, 0), "{:?}", backend);
        }
    }
}

/// Eight products of free witnesses: one multiplier each, no linear slots.
#[test]
fn free_products_cost_one_multiplier_each() {
    for backend in BACKENDS {
        let (res, cost) = run(backend, |cs, prover| {
            for i in 0..8u64 {
                let a = cs.witness(val(prover, i + 2))?;
                let b = cs.witness(val(prover, i + 3))?;
                let o = cs.multiply(a.into(), b.into())?;
                cs.constrain(Lc::from(o) - Scalar::from((i + 2) * (i + 3)));
            }
            Ok(())
        });
        res.unwrap();
        assert_eq!((cost.gates(Backend::Bp), cost.gates(Backend::Bppp), cost.linear(Backend::Bppp)), (8, 8, 0), "{:?}", backend);
    }
}

/// A witness alone in two products is folded into the first; the second reads the wire.
#[test]
fn same_witness_in_two_products() {
    for backend in BACKENDS {
        let (res, cost) = run(backend, |cs, prover| {
            let a = cs.witness(val(prover, 3))?;
            let (b, c) = (cs.witness(val(prover, 5))?, cs.witness(val(prover, 7))?);
            let ab = cs.multiply(a.into(), b.into())?;
            cs.constrain_product(a.into(), c.into(), Lc::from(Scalar::from(21u64)))?;
            cs.constrain(Lc::from(ab) - Scalar::from(15u64));
            Ok(())
        });
        res.unwrap();
        assert_eq!((cost.gates(Backend::Bp), cost.gates(Backend::Bppp), cost.linear(Backend::Bppp)), (2, 2, 0), "{:?}", backend);
    }
}

/// Where else the folded witness is used: each use must read the product's wire.
#[derive(Clone, Copy, Debug)]
enum Use {
    Constraint,
    Lookup,
    Reciprocal,
    Product,
}

const USES: [Use; 4] = [Use::Constraint, Use::Lookup, Use::Reciprocal, Use::Product];

/// `a * b = 12` with `a` folded into the product's left wire, `a = 3` enforced by `u`, and a
/// spare free witness `d = 3` that a wrong substitution could read instead of the wire. The
/// prover's `a` is `a_val` (`b = 12 / a_val`).
fn folded(cs: &mut dyn ConstraintSystem<Scalar>, prover: bool, u: Use, a_val: u64) -> Result<(), R1CSError> {
    let d = cs.witness(val(prover, 3))?;
    let a = cs.witness(val(prover, a_val))?;
    let b = cs.witness(val(prover, 12 / a_val))?;
    let ab = cs.multiply(a.into(), b.into())?;
    cs.constrain(Lc::from(ab) - Scalar::from(12u64));
    cs.constrain(Lc::from(d) - Scalar::from(3u64));
    match u {
        Use::Constraint => cs.constrain(Lc::from(a) - Scalar::from(3u64)),
        Use::Lookup => {
            let t = cs.table(vec![vec![3, 9]])?;
            let sq = cs.witness(val(prover, 9))?;
            cs.lookup(t, &[a.into(), sq.into()])?;
        }
        Use::Reciprocal => {
            let r = cs.reciprocal(1)?;
            r.add(cs, &[a.into()])?;
            r.add_public(cs, -Lc::from(Scalar::ONE), &[3])?;
        }
        Use::Product => cs.constrain_product(Lc::from(Scalar::from(2u64)), a.into(), Lc::from(Scalar::from(6u64)))?,
    }
    Ok(())
}

#[test]
fn folded_witness_is_constrained_everywhere() {
    for backend in BACKENDS {
        for u in USES {
            let (res, cost) = run(backend, |cs, prover| folded(cs, prover, u, 3));
            res.unwrap_or_else(|e| panic!("{:?} {:?}: {:?}", backend, u, e));
            // `a` and `b` are the wires of the first product
            let (_, plain) = run(backend, |cs, prover| {
                let d = cs.witness(val(prover, 3))?;
                cs.constrain(Lc::from(d) - Scalar::from(3u64));
                Ok(())
            });
            assert!(cost.linear(Backend::Bppp) <= plain.linear(Backend::Bppp) + 2, "{:?} {:?}: {:?}", backend, u, cost);
        }
    }
}

/// With the prover's own checks off, `a = 4` (and `b = 3`) satisfies the product but not
/// the use: every backend must reject.
#[cfg(feature = "cheats")]
#[test]
fn folded_witness_cannot_be_forged() {
    for backend in BACKENDS {
        for u in USES {
            let (res, _) = cheats::with_unchecked_prover(|| run(backend, |cs, prover| folded(cs, prover, u, if prover { 4 } else { 3 })));
            assert!(res.is_err(), "{:?} {:?}: a forged folded witness verified", backend, u);
        }
    }
}

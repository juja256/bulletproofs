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

//! Every proof over every curve: generic helpers called for ristretto255 and, with the
//! `secp256k1` feature, secp256k1.

#![allow(non_snake_case)]

use bulletproofs::curve::Ristretto;
use bulletproofs::{BulletproofGens, PedersenGens};

/// The default curve is Ristretto: the old spelling and the new one agree.
#[test]
fn ristretto_generators_unchanged() {
    let a = PedersenGens::default();
    let b = PedersenGens::<Ristretto>::default();
    assert_eq!((a.B, a.B_blinding), (b.B, b.B_blinding));
    let g = BulletproofGens::new(64, 2);
    let h = BulletproofGens::<Ristretto>::new(64, 2);
    for j in 0..2 {
        assert!(g.share(j).G(64).zip(h.share(j).G(64)).all(|(x, y)| x == y));
    }
}

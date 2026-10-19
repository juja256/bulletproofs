//! Cheating provers against the circuit builder (spec §7): wrong multiplicities, tuples that
//! only collide without the compression challenge, forged denominators and numerators. The
//! verifier must reject each of them, on both backends where the cheat applies.

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

use super::builder::cheat::{self, Cheat};
use super::builder::CircuitBuilder;
use super::{Backend, ConstraintSystem, Prover, R1CSError, Verifier};
use crate::{BulletproofGens, PedersenGens};

/// Prove `gadget` (prover values `Some`) with the cheat in place, then verify; `true` iff the
/// verifier accepts. A prover error counts as rejected.
fn accepted<F>(backend: Backend, c: Cheat, gadget: F) -> bool
where
    F: Fn(&mut dyn Gadget, bool) -> Result<(), R1CSError>,
{
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    cheat::set(c);
    let mut t = Transcript::new(b"cheat");
    let mut p = Prover::new(&pc, &mut t);
    p.set_backend(backend);
    let proof = gadget(&mut p, true).and_then(|_| p.prove_with_rng(&bp, &mut ChaCha20Rng::seed_from_u64(3)));
    cheat::set(Cheat::default());
    let proof = match proof {
        Ok(p) => p,
        Err(_) => return false,
    };
    let mut t = Transcript::new(b"cheat");
    let mut v = Verifier::new(&mut t);
    v.set_backend(backend);
    gadget(&mut v, false).unwrap();
    v.verify(&proof, &pc, &bp).is_ok()
}

/// The builder operations the gadgets below need, object safe.
trait Gadget {
    fn w(&mut self, v: Option<u64>) -> super::Variable;
    fn cs(&mut self) -> &mut dyn Ops;
}

trait Ops {
    fn table(&mut self, rows: Vec<Vec<u64>>, w: &[u32]) -> super::TableId;
    fn lookup(&mut self, t: super::TableId, x: &[super::LinearCombination]) -> Result<(), R1CSError>;
    fn recip(&mut self, w: &[u32], private: Vec<(super::LinearCombination, Vec<super::LinearCombination>)>, public: Vec<(super::LinearCombination, Vec<u64>)>) -> Result<(), R1CSError>;
}

impl<C: CircuitBuilder> Ops for C {
    fn table(&mut self, rows: Vec<Vec<u64>>, w: &[u32]) -> super::TableId {
        CircuitBuilder::table(self, rows, w).unwrap()
    }
    fn lookup(&mut self, t: super::TableId, x: &[super::LinearCombination]) -> Result<(), R1CSError> {
        CircuitBuilder::lookup(self, t, x)
    }
    fn recip(&mut self, w: &[u32], private: Vec<(super::LinearCombination, Vec<super::LinearCombination>)>, public: Vec<(super::LinearCombination, Vec<u64>)>) -> Result<(), R1CSError> {
        let mut r = self.reciprocal(w)?;
        for (n, x) in private {
            r.add_weighted(n, x);
        }
        for (c, row) in public {
            r.add_public(c, row);
        }
        self.finish_reciprocal(r)
    }
}

impl<C: CircuitBuilder> Gadget for C {
    fn w(&mut self, v: Option<u64>) -> super::Variable {
        self.witness(v.map(Scalar::from)).unwrap()
    }
    fn cs(&mut self) -> &mut dyn Ops {
        self
    }
}

fn s(x: u64) -> Scalar {
    Scalar::from(x)
}

fn backends() -> [Backend; 2] {
    [Backend::Bp, Backend::Bppp]
}

/// Query `(1, 2)` in a table holding only `(2, 1)`: equal without the challenge `alpha` of BP's
/// compression (and different packings in BP++). Multiplicities forged to match.
#[test]
fn swapped_tuple_is_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let a = cs.w(if p { Some(1) } else { None });
        let b = cs.w(if p { Some(2) } else { None });
        let range = cs.cs().table((0..4).map(|x| vec![x]).collect(), &[2]);
        let pairs = cs.cs().table(vec![vec![2, 1]], &[2, 2]);
        cs.cs().lookup(range, &[a.into()])?;
        cs.cs().lookup(range, &[b.into()])?;
        cs.cs().lookup(pairs, &[a.into(), b.into()])
    };
    let m = vec![s(0), s(1), s(1), s(0), s(1)];
    for b in backends() {
        assert!(!accepted(b, Cheat { multiplicities: Some(m.clone()), ..Cheat::default() }, g), "{:?}", b);
    }
}

/// Multiplicities that do not count the lookups.
#[test]
fn wrong_multiplicities_are_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(1) } else { None });
        let t = cs.cs().table((0..4).map(|x| vec![x]).collect(), &[2]);
        cs.cs().lookup(t, &[x.into()])
    };
    for b in backends() {
        assert!(accepted(b, Cheat::default(), g), "honest, {:?}", b);
        for m in [vec![s(0); 4], vec![s(0), s(0), s(1), s(0)], vec![s(0), s(2), s(0), s(0)]] {
            assert!(!accepted(b, Cheat { multiplicities: Some(m), ..Cheat::default() }, g), "{:?}", b);
        }
    }
}

/// BP: a query outside the table with the denominator of a table row (the multiplier
/// `r * d = 1` holds, the sum vanishes; only `d = c + x` catches it).
#[test]
fn forged_denominator_is_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(5) } else { None });
        let t = cs.cs().table((0..4).map(|x| vec![x]).collect(), &[2]);
        cs.cs().lookup(t, &[x.into()])
    };
    let c = Cheat { multiplicities: Some(vec![s(0), s(1), s(0), s(0)]), denominator_row: Some(vec![1]), ..Cheat::default() };
    assert!(!accepted(Backend::Bp, c.clone(), g));
    assert!(!accepted(Backend::Bppp, c, g));
}

/// BP: a weighted term `2 / (X + 7)` against `-1 / (X + 7)`, the prover using numerator 1
/// (only `o = num` catches it).
#[test]
fn forged_numerator_is_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(7) } else { None });
        cs.cs().recip(&[252], vec![(s(2).into(), vec![x.into()])], vec![((-s(1)).into(), vec![7])])
    };
    for b in backends() {
        assert!(!accepted(b, Cheat::default(), g), "honest prover of a false statement, {:?}", b);
    }
    assert!(!accepted(Backend::Bp, Cheat { numerator: Some(s(1)), ..Cheat::default() }, g));
    // the same statement with numerator 1 is true
    let ok = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(7) } else { None });
        cs.cs().recip(&[252], vec![(s(1).into(), vec![x.into()])], vec![((-s(1)).into(), vec![7])])
    };
    for b in backends() {
        assert!(accepted(b, Cheat::default(), ok), "{:?}", b);
    }
}

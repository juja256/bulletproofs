//! Cheating provers against the circuit builder (spec §7): wrong multiplicities, tuples that
//! only collide without the compression challenge, forged denominators and numerators. The
//! verifier must reject each of them, on both backends where the cheat applies.

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

use super::builder::cheat::{self, Cheat};
use super::builder::CircuitBuilder;
use super::{Backend, Prover, R1CSError, Verifier};
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
    fn table(&mut self, rows: Vec<Vec<u64>>) -> super::TableId;
    fn lookup(&mut self, t: super::TableId, x: &[super::LinearCombination]) -> Result<(), R1CSError>;
    fn witness_scalar(&mut self, v: Option<Scalar>) -> Result<super::Variable, R1CSError>;
    /// A multiplier `l * 1 = o` with `l = v`; `wire` gets its left wire.
    fn product_wire(&mut self, v: Option<Scalar>, wire: &mut Option<super::Variable>) -> Result<(), R1CSError>;
    fn recip(&mut self, m: usize, private: Vec<(super::LinearCombination, Vec<super::LinearCombination>)>, public: Vec<(super::LinearCombination, Vec<u64>)>) -> Result<(), R1CSError>;
}

impl<C: CircuitBuilder> Ops for C {
    fn table(&mut self, rows: Vec<Vec<u64>>) -> super::TableId {
        CircuitBuilder::table(self, rows).unwrap()
    }
    fn lookup(&mut self, t: super::TableId, x: &[super::LinearCombination]) -> Result<(), R1CSError> {
        CircuitBuilder::lookup(self, t, x)
    }
    fn witness_scalar(&mut self, v: Option<Scalar>) -> Result<super::Variable, R1CSError> {
        self.witness(v)
    }
    fn product_wire(&mut self, v: Option<Scalar>, wire: &mut Option<super::Variable>) -> Result<(), R1CSError> {
        let (l, _, o) = self.allocate_multiplier(v.map(|v| (v, Scalar::ONE)))?;
        self.constrain(o - l);
        *wire = Some(l);
        Ok(())
    }
    fn recip(&mut self, m: usize, private: Vec<(super::LinearCombination, Vec<super::LinearCombination>)>, public: Vec<(super::LinearCombination, Vec<u64>)>) -> Result<(), R1CSError> {
        let r = self.reciprocal(m)?;
        for (n, x) in private {
            r.add_weighted(self, n, &x)?;
        }
        for (c, row) in public {
            r.add_public(self, c, &row)?;
        }
        Ok(())
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

/// Query `(1, 2)` in a table holding only `(2, 1)`: equal without the compression challenge
/// (BP: `alpha`; BP++: `eta`). Multiplicities forged to match.
#[test]
fn swapped_tuple_is_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let a = cs.w(if p { Some(1) } else { None });
        let b = cs.w(if p { Some(2) } else { None });
        let pairs = cs.cs().table(vec![vec![2, 1]]);
        cs.cs().lookup(pairs, &[a.into(), b.into()])
    };
    for b in backends() {
        assert!(!accepted(b, Cheat { multiplicities: Some(vec![s(1)]), ..Cheat::default() }, g), "{:?}", b);
    }
}

/// Unbounded components (spec §7.3): a base-16 packing would map `(3 + 16, 5 - 1)` and
/// `(3 + 2^128, 5 - 2^124)` to the row `(3, 5)`; neither is a row. Every component may be a
/// fresh witness, a product wire (copied into `C_O` on BP++) or carry a constant.
#[test]
fn packed_collisions_are_rejected() {
    use super::{LinearCombination, Variable};
    let big = |e: u32| (0..e).fold(Scalar::ONE, |a, _| a + a);
    let cheats: [(Scalar, Scalar); 2] = [(s(19), s(4)), (s(3) + big(128), s(5) - big(124))];
    for (i, (x0, x1)) in cheats.iter().copied().enumerate() {
        for wire in [false, true] {
            let g = move |cs: &mut dyn Gadget, p: bool| {
                let a_val = if p { Some(x0) } else { None };
                // the first component as a fresh witness or as the left wire of a product
                let first: LinearCombination = if wire {
                    let mut l = None;
                    cs.cs().product_wire(a_val, &mut l)?;
                    l.unwrap().into()
                } else {
                    cs.cs().witness_scalar(a_val)?.into()
                };
                let b = cs.cs().witness_scalar(if p { Some(x1 - s(1)) } else { None })?;
                let rows: Vec<Vec<u64>> = (0..16u64).map(|i| vec![i, (i + 2) % 16]).collect();
                let t = cs.cs().table(rows);
                cs.cs().lookup(t, &[first, Variable::from(b) + Scalar::ONE])
            };
            let mut m = vec![s(0); 16];
            m[3] = s(1);
            for b in backends() {
                assert!(!accepted(b, Cheat { multiplicities: Some(m.clone()), ..Cheat::default() }, g), "cheat {} wire {} {:?}", i, wire, b);
                assert!(!accepted(b, Cheat::default(), g), "cheat {} wire {} {:?}: honest counting", i, wire, b);
            }
        }
    }
    // the honest statement (3, 5) is accepted in both forms
    for wire in [false, true] {
        let g = move |cs: &mut dyn Gadget, p: bool| {
            let first: LinearCombination = if wire {
                let mut l = None;
                cs.cs().product_wire(if p { Some(s(3)) } else { None }, &mut l)?;
                l.unwrap().into()
            } else {
                cs.cs().witness_scalar(if p { Some(s(3)) } else { None })?.into()
            };
            let b = cs.cs().witness_scalar(if p { Some(s(4)) } else { None })?;
            let rows: Vec<Vec<u64>> = (0..16u64).map(|i| vec![i, (i + 2) % 16]).collect();
            let t = cs.cs().table(rows);
            cs.cs().lookup(t, &[first, Variable::from(b) + Scalar::ONE])
        };
        for b in backends() {
            assert!(accepted(b, Cheat::default(), g), "honest, wire {} {:?}", wire, b);
        }
    }
}

/// Multiplicities that do not count the lookups.
#[test]
fn wrong_multiplicities_are_rejected() {
    let g = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(1) } else { None });
        let t = cs.cs().table((0..4).map(|x| vec![x]).collect());
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
        let t = cs.cs().table((0..4).map(|x| vec![x]).collect());
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
        cs.cs().recip(1, vec![(s(2).into(), vec![x.into()])], vec![((-s(1)).into(), vec![7])])
    };
    for b in backends() {
        assert!(!accepted(b, Cheat::default(), g), "honest prover of a false statement, {:?}", b);
    }
    assert!(!accepted(Backend::Bp, Cheat { numerator: Some(s(1)), ..Cheat::default() }, g));
    // the same statement with numerator 1 is true
    let ok = |cs: &mut dyn Gadget, p: bool| {
        let x = cs.w(if p { Some(7) } else { None });
        cs.cs().recip(1, vec![(s(1).into(), vec![x.into()])], vec![((-s(1)).into(), vec![7])])
    };
    for b in backends() {
        assert!(accepted(b, Cheat::default(), ok), "{:?}", b);
    }
}

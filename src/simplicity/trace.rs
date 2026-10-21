//! The tracer: the crate's own BP++ verifier, run over a scalar type that records every
//! operation on a tape ([`Traced`]) and a curve whose points remember where they came from
//! ([`TracedCurve`]). Operations on constants fold; a scalar from the proof or from a challenge
//! starts a node. The tape is the verifier's scalar arithmetic as a straight-line program.
//!
//! The verifier's control flow depends only on the circuit's shape; the only value-dependent
//! branches are checks ("not zero", equality with a constant), which become assertions on the
//! tape. A comparison of two traced values for equality is refused.

use core::fmt;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::cell::RefCell;
use std::collections::HashMap;

use k256::elliptic_curve::ff::PrimeField as _;
use k256::{ProjectivePoint, Scalar as K};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::curve::{Curve, Field, PointEncoding, Secp256k1, Secp256k1Compressed};
use crate::simplicity::sha::Part;

/// A node of the tape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct NodeId(pub u32);

/// An operation of the tape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TOp {
    /// The proof's scalar number `i`.
    WitScalar(usize),
    /// The scalar of the transcript's challenge number `k` (from 64 bytes).
    Challenge(usize),
    Add(NodeId, NodeId),
    Sub(NodeId, NodeId),
    Mul(NodeId, NodeId),
    Neg(NodeId),
    Invert(NodeId),
    /// `a + c`.
    AddC(NodeId, ScalarBytes),
    /// `a · c`.
    MulC(NodeId, ScalarBytes),
    /// A check: `a ≠ 0`.
    AssertNonzero(NodeId),
    /// A check: `a = c`.
    AssertEq(NodeId, ScalarBytes),
    /// A check: `a ≠ c`.
    AssertNe(NodeId, ScalarBytes),
}

/// A constant in an operation (big-endian), hashable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ScalarBytes(pub [u8; 32]);

impl ScalarBytes {
    fn of(k: &K) -> Self {
        let mut b = [0u8; 32];
        b.copy_from_slice(&k.to_repr());
        ScalarBytes(b)
    }
    /// The scalar.
    #[cfg_attr(not(test), allow(dead_code))] // the numeric model (tests)
    pub(crate) fn scalar(&self) -> K {
        Option::from(K::from_repr(self.0.into())).expect("a canonical constant")
    }
}

impl TOp {
    /// Whether the operation is a check (a root of the program, never removed).
    pub(crate) fn is_check(&self) -> bool {
        matches!(self, TOp::AssertNonzero(_) | TOp::AssertEq(..) | TOp::AssertNe(..))
    }

    /// The nodes it reads.
    pub(crate) fn args(&self) -> Vec<NodeId> {
        match *self {
            TOp::WitScalar(_) | TOp::Challenge(_) => vec![],
            TOp::Add(a, b) | TOp::Sub(a, b) | TOp::Mul(a, b) => vec![a, b],
            TOp::Neg(a) | TOp::Invert(a) | TOp::AddC(a, _) | TOp::MulC(a, _) => vec![a],
            TOp::AssertNonzero(a) | TOp::AssertEq(a, _) | TOp::AssertNe(a, _) => vec![a],
        }
    }
}

/// The recorded program: operations and the value each had when traced.
#[derive(Clone, Debug, Default)]
pub(crate) struct Tape {
    pub ops: Vec<TOp>,
    pub values: Vec<K>,
}

impl Tape {
    /// The operations without values: equal for two proofs of one circuit.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn structure(&self) -> Vec<TOp> {
        self.ops.clone()
    }

    /// Recompute every node from the proof's scalars and the challenges (the numeric model of
    /// the program); checks evaluate to their input. Panics on a failing check.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn eval(&self, wit: &[K], chal: &[K]) -> Vec<K> {
        let mut v: Vec<K> = Vec::with_capacity(self.ops.len());
        for op in &self.ops {
            let g = |n: NodeId| v[n.0 as usize];
            let x = match *op {
                TOp::WitScalar(i) => wit[i],
                TOp::Challenge(k) => chal[k],
                TOp::Add(a, b) => g(a) + g(b),
                TOp::Sub(a, b) => g(a) - g(b),
                TOp::Mul(a, b) => g(a) * g(b),
                TOp::Neg(a) => -g(a),
                TOp::Invert(a) => Option::from(g(a).invert()).expect("checked nonzero"),
                TOp::AddC(a, c) => g(a) + c.scalar(),
                TOp::MulC(a, c) => g(a) * c.scalar(),
                TOp::AssertNonzero(a) => {
                    assert!(!bool::from(g(a).is_zero()), "a check failed");
                    g(a)
                }
                TOp::AssertEq(a, c) => {
                    assert_eq!(g(a), c.scalar(), "a check failed");
                    g(a)
                }
                TOp::AssertNe(a, c) => {
                    assert_ne!(g(a), c.scalar(), "a check failed");
                    g(a)
                }
            };
            v.push(x);
        }
        v
    }

    /// The nodes needed by the checks and by `roots`, in tape order (dead code removed).
    pub(crate) fn live(&self, roots: &[NodeId]) -> Vec<bool> {
        let mut live = vec![false; self.ops.len()];
        for (i, op) in self.ops.iter().enumerate() {
            if op.is_check() {
                live[i] = true;
            }
        }
        for r in roots {
            live[r.0 as usize] = true;
        }
        for i in (0..self.ops.len()).rev() {
            if live[i] {
                for a in self.ops[i].args() {
                    live[a.0 as usize] = true;
                }
            }
        }
        live
    }
}

/// The tracer's state: the tape, its sharing table and the provenance registries.
#[derive(Default)]
struct Ctx {
    tape: Tape,
    share: HashMap<TOp, NodeId>,
    wit_points: HashMap<Vec<u8>, usize>,
    wit_scalars: HashMap<[u8; 32], usize>,
    node_bytes: HashMap<[u8; 32], NodeId>,
    challenges: HashMap<Vec<u8>, usize>,
}

thread_local! {
    static CTX: RefCell<Option<Ctx>> = RefCell::new(None);
}

/// Run `f` with a fresh tape; returns its result and the tape.
pub(crate) fn with_tape<R>(f: impl FnOnce() -> R) -> (R, Tape) {
    CTX.with(|c| *c.borrow_mut() = Some(Ctx::default()));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    let ctx = CTX.with(|c| c.borrow_mut().take()).expect("tracing");
    match r {
        Ok(r) => (r, ctx.tape),
        Err(e) => std::panic::resume_unwind(e),
    }
}

fn with_ctx<R>(f: impl FnOnce(&mut Ctx) -> R) -> R {
    CTX.with(|c| f(c.borrow_mut().as_mut().expect("a traced operation outside with_tape")))
}

fn tracing() -> bool {
    CTX.with(|c| c.borrow().is_some())
}

/// Record an operation with its value (shared if recorded before).
fn record(op: TOp, value: K) -> NodeId {
    with_ctx(|c| {
        if !op.is_check() {
            if let Some(n) = c.share.get(&op) {
                return *n;
            }
        }
        let n = NodeId(c.tape.ops.len() as u32);
        c.tape.ops.push(op);
        c.tape.values.push(value);
        if !op.is_check() {
            c.share.insert(op, n);
        }
        n
    })
}

/// The proof's point `c` is witness point number `i`.
pub(crate) fn register_witness_point(c: &Secp256k1Compressed, i: usize) {
    with_ctx(|x| x.wit_points.insert(c.as_bytes().to_vec(), i));
}

/// The proof's scalar with encoding `b` is witness scalar number `i`.
pub(crate) fn register_witness_scalar(b: &[u8; 32], i: usize) {
    with_ctx(|x| x.wit_scalars.insert(*b, i));
}

/// Provenance of bytes a transcript absorbs (none outside tracing).
pub(crate) fn provenance(bytes: &[u8]) -> Option<Part> {
    if !tracing() {
        return None;
    }
    with_ctx(|c| {
        if let Some(i) = c.wit_points.get(bytes) {
            return Some(Part::WitPoint(*i));
        }
        if bytes.len() == 32 {
            let mut b = [0u8; 32];
            b.copy_from_slice(bytes);
            if let Some(n) = c.node_bytes.get(&b) {
                return Some(Part::Scalar(n.0));
            }
        }
        None
    })
}

/// The output of the transcript's challenge number `k`.
pub(crate) fn note_challenge(k: usize, bytes: &[u8]) {
    if tracing() {
        with_ctx(|c| c.challenges.insert(bytes.to_vec(), k));
    }
}

/// A traced scalar: its value and, unless it is a constant, its node.
#[derive(Clone, Copy)]
pub(crate) struct Traced {
    pub value: K,
    pub node: Option<NodeId>,
}

impl fmt::Debug for Traced {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Traced({:?}, {:?})", self.node, self.value)
    }
}

impl Traced {
    /// A constant.
    pub(crate) const fn constant(value: K) -> Self {
        Traced { value, node: None }
    }

    /// The proof's scalar number `i` (for tests and the compiler).
    pub(crate) fn witness(i: usize, value: K) -> Self {
        Traced { value, node: Some(record(TOp::WitScalar(i), value)) }
    }

    fn node(op: TOp, value: K) -> Self {
        Traced { value, node: Some(record(op, value)) }
    }

    fn bytes_of_node(&self) {
        if let Some(n) = self.node {
            let b = ScalarBytes::of(&self.value).0;
            with_ctx(|c| c.node_bytes.insert(b, n));
        }
    }

    /// A check that `self` equals `other`: records the observed outcome; refuses two nodes
    /// that are equal (the program could not tell which branch an honest proof takes).
    fn traced_eq(&self, other: &Self) -> bool {
        let eq = self.value == other.value;
        match (self.node, other.node) {
            (None, None) => eq,
            (Some(a), Some(b)) if a == b => true,
            (Some(a), None) | (None, Some(a)) => {
                let c = ScalarBytes::of(if self.node.is_some() { &other.value } else { &self.value });
                record(if eq { TOp::AssertEq(a, c) } else { TOp::AssertNe(a, c) }, self.value);
                eq
            }
            (Some(a), Some(b)) => {
                if eq {
                    panic!("trace: equality of two traced values");
                }
                let d = record(TOp::Sub(a, b), self.value - other.value);
                record(TOp::AssertNonzero(d), self.value - other.value);
                false
            }
        }
    }
}

impl Default for Traced {
    fn default() -> Self {
        Traced::constant(K::ZERO)
    }
}

impl PartialEq for Traced {
    fn eq(&self, other: &Self) -> bool {
        self.traced_eq(other)
    }
}

impl Eq for Traced {}

impl ConstantTimeEq for Traced {
    fn ct_eq(&self, other: &Self) -> Choice {
        Choice::from(self.traced_eq(other) as u8)
    }
}

impl ConditionallySelectable for Traced {
    /// The selected value (a branch on `choice`, which comes from a check the tape records:
    /// `invert().unwrap_or(..)` after its nonzero check).
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        if bool::from(choice) {
            *b
        } else {
            *a
        }
    }
}

impl zeroize::Zeroize for Traced {
    fn zeroize(&mut self) {}
}

impl serde::Serialize for Traced {
    fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
        Err(serde::ser::Error::custom("a traced scalar is not serialized"))
    }
}

impl<'de> serde::Deserialize<'de> for Traced {
    fn deserialize<D: serde::Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        Err(serde::de::Error::custom("a traced scalar is not deserialized"))
    }
}

impl From<u64> for Traced {
    fn from(x: u64) -> Self {
        Traced::constant(K::from(x))
    }
}

fn add(x: Traced, y: Traced) -> Traced {
    let v = x.value + y.value;
    match (x.node, y.node) {
        (None, None) => Traced::constant(v),
        (Some(a), None) => {
            if bool::from(y.value.is_zero()) {
                x
            } else {
                Traced::node(TOp::AddC(a, ScalarBytes::of(&y.value)), v)
            }
        }
        (None, Some(_)) => add(y, x),
        (Some(a), Some(b)) => Traced::node(TOp::Add(a.min(b), a.max(b)), v),
    }
}

fn neg(x: Traced) -> Traced {
    match x.node {
        None => Traced::constant(-x.value),
        Some(a) => Traced::node(TOp::Neg(a), -x.value),
    }
}

fn sub(x: Traced, y: Traced) -> Traced {
    let v = x.value - y.value;
    match (x.node, y.node) {
        (None, None) => Traced::constant(v),
        (Some(_), None) => add(x, Traced::constant(-y.value)),
        (None, Some(_)) => add(neg(y), x),
        (Some(a), Some(b)) => Traced::node(TOp::Sub(a, b), v),
    }
}

fn mul(x: Traced, y: Traced) -> Traced {
    let v = x.value * y.value;
    match (x.node, y.node) {
        (None, None) => Traced::constant(v),
        (Some(a), None) => {
            if bool::from(y.value.is_zero()) {
                Traced::constant(K::ZERO)
            } else if y.value == K::ONE {
                x
            } else {
                Traced::node(TOp::MulC(a, ScalarBytes::of(&y.value)), v)
            }
        }
        (None, Some(_)) => mul(y, x),
        (Some(a), Some(b)) => Traced::node(TOp::Mul(a.min(b), a.max(b)), v),
    }
}

macro_rules! ops {
    ($Tr:ident, $f:ident, $Assign:ident, $fa:ident, $g:path) => {
        impl $Tr for Traced {
            type Output = Traced;
            fn $f(self, o: Traced) -> Traced {
                $g(self, o)
            }
        }
        impl<'a> $Tr<&'a Traced> for Traced {
            type Output = Traced;
            fn $f(self, o: &'a Traced) -> Traced {
                $g(self, *o)
            }
        }
        impl<'a, 'b> $Tr<&'b Traced> for &'a Traced {
            type Output = Traced;
            fn $f(self, o: &'b Traced) -> Traced {
                $g(*self, *o)
            }
        }
        impl<'a> $Tr<Traced> for &'a Traced {
            type Output = Traced;
            fn $f(self, o: Traced) -> Traced {
                $g(*self, o)
            }
        }
        impl $Assign for Traced {
            fn $fa(&mut self, o: Traced) {
                *self = $g(*self, o)
            }
        }
        impl<'a> $Assign<&'a Traced> for Traced {
            fn $fa(&mut self, o: &'a Traced) {
                *self = $g(*self, *o)
            }
        }
    };
}

ops!(Add, add, AddAssign, add_assign, add);
ops!(Sub, sub, SubAssign, sub_assign, sub);
ops!(Mul, mul, MulAssign, mul_assign, mul);

impl Neg for Traced {
    type Output = Traced;
    fn neg(self) -> Traced {
        neg(self)
    }
}

impl<'a> Neg for &'a Traced {
    type Output = Traced;
    fn neg(self) -> Traced {
        neg(*self)
    }
}

impl Sum for Traced {
    fn sum<I: Iterator<Item = Traced>>(it: I) -> Traced {
        it.fold(Traced::constant(K::ZERO), add)
    }
}

impl<'a> Sum<&'a Traced> for Traced {
    fn sum<I: Iterator<Item = &'a Traced>>(it: I) -> Traced {
        it.fold(Traced::constant(K::ZERO), |a, b| add(a, *b))
    }
}

impl Product for Traced {
    fn product<I: Iterator<Item = Traced>>(it: I) -> Traced {
        it.fold(Traced::constant(K::ONE), mul)
    }
}

impl<'a> Product<&'a Traced> for Traced {
    fn product<I: Iterator<Item = &'a Traced>>(it: I) -> Traced {
        it.fold(Traced::constant(K::ONE), |a, b| mul(a, *b))
    }
}

impl ff::Field for Traced {
    const ZERO: Self = Traced::constant(K::ZERO);
    const ONE: Self = Traced::constant(K::ONE);

    fn random(rng: impl RngCore) -> Self {
        Traced::constant(K::random(rng))
    }

    fn square(&self) -> Self {
        mul(*self, *self)
    }

    fn double(&self) -> Self {
        add(*self, *self)
    }

    fn invert(&self) -> CtOption<Self> {
        match self.node {
            None => self.value.invert().map(Traced::constant),
            Some(a) => {
                if bool::from(self.value.is_zero()) {
                    panic!("trace: inverting a zero traced value");
                }
                record(TOp::AssertNonzero(a), self.value);
                let inv = self.value.invert().unwrap();
                CtOption::new(Traced::node(TOp::Invert(a), inv), Choice::from(1))
            }
        }
    }

    fn sqrt_ratio(_: &Self, _: &Self) -> (Choice, Self) {
        panic!("trace: sqrt_ratio is not traceable")
    }
}

impl ff::PrimeField for Traced {
    type Repr = k256::FieldBytes;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut b = [0u8; 32];
        b.copy_from_slice(&repr);
        match Field::from_bytes32(&b) {
            Some(t) => CtOption::new(t, Choice::from(1)),
            None => CtOption::new(Traced::constant(K::ZERO), Choice::from(0)),
        }
    }

    fn to_repr(&self) -> Self::Repr {
        self.bytes_of_node();
        self.value.to_repr()
    }

    fn is_odd(&self) -> Choice {
        assert!(self.node.is_none(), "trace: is_odd is not traceable");
        self.value.is_odd()
    }

    const MODULUS: &'static str = K::MODULUS;
    const NUM_BITS: u32 = K::NUM_BITS;
    const CAPACITY: u32 = K::CAPACITY;
    const TWO_INV: Self = Traced::constant(K::TWO_INV);
    const MULTIPLICATIVE_GENERATOR: Self = Traced::constant(K::MULTIPLICATIVE_GENERATOR);
    const S: u32 = K::S;
    const ROOT_OF_UNITY: Self = Traced::constant(K::ROOT_OF_UNITY);
    const ROOT_OF_UNITY_INV: Self = Traced::constant(K::ROOT_OF_UNITY_INV);
    const DELTA: Self = Traced::constant(K::DELTA);
}

impl Field for Traced {
    fn from_wide(bytes: &[u8; 64]) -> Self {
        let value = <K as Field>::from_wide(bytes);
        let k = if tracing() { with_ctx(|c| c.challenges.get(&bytes[..]).copied()) } else { None };
        match k {
            Some(k) => Traced::node(TOp::Challenge(k), value),
            None => Traced::constant(value),
        }
    }

    fn to_bytes32(&self) -> [u8; 32] {
        self.bytes_of_node();
        ScalarBytes::of(&self.value).0
    }

    fn from_bytes32(bytes: &[u8; 32]) -> Option<Self> {
        let value = <K as Field>::from_bytes32(bytes)?;
        let i = if tracing() { with_ctx(|c| c.wit_scalars.get(bytes).copied()) } else { None };
        Some(match i {
            Some(i) => {
                let t = Traced::witness(i, value);
                t.bytes_of_node();
                t
            }
            None => Traced::constant(value),
        })
    }
}

/// Where a point came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PointSrc {
    /// A constant of the program (generators, the statement's commitments).
    Const,
    /// The proof's point number `i`.
    Witness(usize),
}

/// A point with its origin.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TracedPoint {
    pub value: ProjectivePoint,
    pub src: PointSrc,
}

impl TracedPoint {
    pub(crate) fn constant(value: ProjectivePoint) -> Self {
        TracedPoint { value, src: PointSrc::Const }
    }

    fn arith(a: &Self, b: &Self, value: ProjectivePoint) -> Self {
        assert!(a.src == PointSrc::Const && b.src == PointSrc::Const, "trace: arithmetic on a proof point");
        TracedPoint::constant(value)
    }
}

impl PartialEq for TracedPoint {
    fn eq(&self, o: &Self) -> bool {
        self.value == o.value
    }
}

impl Eq for TracedPoint {}

impl ConditionallySelectable for TracedPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        if bool::from(choice) {
            *b
        } else {
            *a
        }
    }
}

impl zeroize::Zeroize for TracedPoint {
    fn zeroize(&mut self) {}
}

macro_rules! point_ops {
    ($Tr:ident, $f:ident, $Assign:ident, $fa:ident, $op:tt) => {
        impl $Tr for TracedPoint {
            type Output = TracedPoint;
            fn $f(self, o: TracedPoint) -> TracedPoint {
                TracedPoint::arith(&self, &o, self.value $op o.value)
            }
        }
        impl<'a> $Tr<&'a TracedPoint> for TracedPoint {
            type Output = TracedPoint;
            fn $f(self, o: &'a TracedPoint) -> TracedPoint {
                TracedPoint::arith(&self, o, self.value $op o.value)
            }
        }
        impl<'a, 'b> $Tr<&'b TracedPoint> for &'a TracedPoint {
            type Output = TracedPoint;
            fn $f(self, o: &'b TracedPoint) -> TracedPoint {
                TracedPoint::arith(self, o, self.value $op o.value)
            }
        }
        impl<'a> $Tr<TracedPoint> for &'a TracedPoint {
            type Output = TracedPoint;
            fn $f(self, o: TracedPoint) -> TracedPoint {
                TracedPoint::arith(self, &o, self.value $op o.value)
            }
        }
        impl $Assign for TracedPoint {
            fn $fa(&mut self, o: TracedPoint) {
                *self = TracedPoint::arith(self, &o, self.value $op o.value)
            }
        }
        impl<'a> $Assign<&'a TracedPoint> for TracedPoint {
            fn $fa(&mut self, o: &'a TracedPoint) {
                *self = TracedPoint::arith(self, o, self.value $op o.value)
            }
        }
    };
}

point_ops!(Add, add, AddAssign, add_assign, +);
point_ops!(Sub, sub, SubAssign, sub_assign, -);

impl Neg for TracedPoint {
    type Output = TracedPoint;
    fn neg(self) -> TracedPoint {
        TracedPoint::arith(&self, &self, -self.value)
    }
}

fn scale(p: &TracedPoint, k: &Traced) -> TracedPoint {
    assert!(k.node.is_none(), "trace: a point times a traced scalar (the MSM is lowered separately)");
    TracedPoint::arith(p, p, p.value * k.value)
}

impl Mul<Traced> for TracedPoint {
    type Output = TracedPoint;
    fn mul(self, k: Traced) -> TracedPoint {
        scale(&self, &k)
    }
}

impl<'a> Mul<&'a Traced> for TracedPoint {
    type Output = TracedPoint;
    fn mul(self, k: &'a Traced) -> TracedPoint {
        scale(&self, k)
    }
}

impl<'a, 'b> Mul<&'b Traced> for &'a TracedPoint {
    type Output = TracedPoint;
    fn mul(self, k: &'b Traced) -> TracedPoint {
        scale(self, k)
    }
}

impl<'a> Mul<Traced> for &'a TracedPoint {
    type Output = TracedPoint;
    fn mul(self, k: Traced) -> TracedPoint {
        scale(self, &k)
    }
}

impl MulAssign<Traced> for TracedPoint {
    fn mul_assign(&mut self, k: Traced) {
        *self = scale(self, &k)
    }
}

impl<'a> MulAssign<&'a Traced> for TracedPoint {
    fn mul_assign(&mut self, k: &'a Traced) {
        *self = scale(self, k)
    }
}

impl Sum for TracedPoint {
    fn sum<I: Iterator<Item = TracedPoint>>(it: I) -> TracedPoint {
        it.fold(TracedPoint::constant(ProjectivePoint::IDENTITY), |a, b| a + b)
    }
}

impl<'a> Sum<&'a TracedPoint> for TracedPoint {
    fn sum<I: Iterator<Item = &'a TracedPoint>>(it: I) -> TracedPoint {
        it.fold(TracedPoint::constant(ProjectivePoint::IDENTITY), |a, b| a + b)
    }
}

impl group::Group for TracedPoint {
    type Scalar = Traced;

    fn random(rng: impl RngCore) -> Self {
        TracedPoint::constant(<ProjectivePoint as group::Group>::random(rng))
    }

    fn identity() -> Self {
        TracedPoint::constant(ProjectivePoint::IDENTITY)
    }

    fn generator() -> Self {
        TracedPoint::constant(ProjectivePoint::GENERATOR)
    }

    fn is_identity(&self) -> Choice {
        self.value.is_identity()
    }

    fn double(&self) -> Self {
        TracedPoint::arith(self, self, self.value.double())
    }
}

/// secp256k1 for the tracer: scalars are [`Traced`], points remember their origin; the
/// multiscalar multiplication is not computed here (the compiler lowers it).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct TracedCurve;

impl Curve for TracedCurve {
    type Scalar = Traced;
    type Point = TracedPoint;
    type Compressed = Secp256k1Compressed;
    const NAME: &'static str = Secp256k1::NAME;
    const POINT_BYTES: usize = Secp256k1::POINT_BYTES;

    fn compress(p: &TracedPoint) -> Secp256k1Compressed {
        Secp256k1::compress(&p.value)
    }

    fn decompress(c: &Secp256k1Compressed) -> Option<TracedPoint> {
        let value = Secp256k1::decompress(c)?;
        let i = if tracing() { with_ctx(|x| x.wit_points.get(c.as_bytes()).copied()) } else { None };
        Some(TracedPoint { value, src: i.map_or(PointSrc::Const, PointSrc::Witness) })
    }

    fn point_from_uniform(bytes: &[u8; 64]) -> TracedPoint {
        TracedPoint::constant(Secp256k1::point_from_uniform(bytes))
    }

    fn default_pedersen() -> (TracedPoint, TracedPoint) {
        let (a, b) = Secp256k1::default_pedersen();
        (TracedPoint::constant(a), TracedPoint::constant(b))
    }

    fn msm_ct(_: &[Traced], _: &[TracedPoint]) -> TracedPoint {
        panic!("trace: the multiscalar multiplication is lowered separately")
    }

    fn msm_vt(_: &[Traced], _: &[TracedPoint]) -> TracedPoint {
        panic!("trace: the multiscalar multiplication is lowered separately")
    }
}

#[cfg(test)]
#[path = "trace_tests.rs"]
mod tests;

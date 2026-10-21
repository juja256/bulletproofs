//! Rewrites of the IR that keep its meaning and make it cheaper to recompute: products as
//! products of squares of their atoms (shared prefixes), sums as balanced trees, common
//! subexpressions merged, dead code dropped. Exact: the scalar jets are arithmetic in F_n.

use std::collections::{BTreeMap, HashMap};

use k256::elliptic_curve::ff::PrimeField as _;

use crate::simplicity::ir::{Op, Prog, Ty, Val};

type K = k256::Scalar;

/// The rewrites, in order.
pub(crate) fn optimize(p: &Prog) -> Prog {
    dce(&monomials(p))
}

/// A product `c · Π a^e` over atoms (values of the program being built).
#[derive(Clone)]
struct Mono {
    c: K,
    f: BTreeMap<Val, u64>,
}

impl Mono {
    fn atom(a: Val) -> Mono {
        Mono { c: K::ONE, f: BTreeMap::from([(a, 1)]) }
    }
    fn constant(c: K) -> Mono {
        Mono { c, f: BTreeMap::new() }
    }
    fn times(&self, o: &Mono) -> Mono {
        let mut f = self.f.clone();
        for (a, e) in &o.f {
            *f.entry(*a).or_insert(0) += e;
        }
        Mono { c: self.c * o.c, f }
    }
}

/// A program under construction that merges equal pure operations (constants, scalar jets).
struct Builder {
    out: Prog,
    jets: HashMap<(&'static str, Vec<Val>), Val>,
    consts: HashMap<(Ty, Vec<u8>), Val>,
    squares: HashMap<(Val, u32), Val>,
}

const PURE: [&str; 4] = ["scalar_multiply", "scalar_add", "scalar_negate", "scalar_invert"];

impl Builder {
    fn new() -> Self {
        Builder { out: Prog::new(), jets: HashMap::new(), consts: HashMap::new(), squares: HashMap::new() }
    }
    fn push(&mut self, op: Op) -> Val {
        match &op {
            Op::Const(t, b) => {
                let key = (t.clone(), b.clone());
                if let Some(v) = self.consts.get(&key) {
                    return *v;
                }
                let v = self.out.push(op);
                self.consts.insert(key, v);
                v
            }
            Op::Jet(n, a, _) if PURE.contains(n) => {
                // multiplication and addition commute: one key for both orders
                let mut args = a.clone();
                if matches!(*n, "scalar_multiply" | "scalar_add") {
                    args.sort();
                }
                let key = (*n, args);
                if let Some(v) = self.jets.get(&key) {
                    return *v;
                }
                let v = self.out.push(op);
                self.jets.insert(key, v);
                v
            }
            _ => self.out.push(op),
        }
    }
    fn mul(&mut self, a: Val, b: Val) -> Val {
        self.push(Op::Jet("scalar_multiply", vec![a, b], Ty::word()))
    }
    fn add(&mut self, a: Val, b: Val) -> Val {
        self.push(Op::Jet("scalar_add", vec![a, b], Ty::word()))
    }
    fn konst(&mut self, c: K) -> Val {
        self.push(Op::Const(Ty::word(), c.to_repr().to_vec()))
    }
    /// `a^(2^j)` by squaring.
    fn square(&mut self, a: Val, j: u32) -> Val {
        if j == 0 {
            return a;
        }
        if let Some(v) = self.squares.get(&(a, j)) {
            return *v;
        }
        let s = self.square(a, j - 1);
        let v = self.mul(s, s);
        self.squares.insert((a, j), v);
        v
    }
    /// A monomial as a product of squares of its atoms, lowest (atom, j) first, folded to the
    /// left: the product for exponent e is the product for e without its last factor, times
    /// that factor (so the powers of one atom share their prefixes); the coefficient last.
    fn emit(&mut self, m: &Mono) -> Val {
        let mut acc: Option<Val> = None;
        for (&a, &e) in &m.f {
            for j in 0..64u32 {
                if (e >> j) & 1 == 1 {
                    let s = self.square(a, j);
                    acc = Some(match acc {
                        None => s,
                        Some(x) => self.mul(x, s),
                    });
                }
            }
        }
        match acc {
            None => self.konst(m.c),
            Some(x) if m.c == K::ONE => x,
            Some(x) => {
                let k = self.konst(m.c);
                self.mul(x, k)
            }
        }
    }
}

/// A canonical scalar constant (below the group order), as a coefficient.
fn scalar_const(op: &Op) -> Option<K> {
    match op {
        Op::Const(Ty::Word(256), b) => {
            let mut r = k256::FieldBytes::default();
            r.copy_from_slice(b);
            Option::from(K::from_repr(r))
        }
        _ => None,
    }
}

/// Products as monomials: a product read only by products is never built; a product read by
/// anything else is built as [`Builder::emit`] when first needed.
fn monomials(p: &Prog) -> Prog {
    let ops = p.ops();
    let mut b = Builder::new();
    let mut built: Vec<Option<Val>> = vec![None; ops.len()];
    let mut mono: Vec<Option<Mono>> = vec![None; ops.len()];
    fn get(b: &mut Builder, built: &mut [Option<Val>], mono: &[Option<Mono>], i: usize) -> Val {
        if let Some(v) = built[i] {
            return v;
        }
        let v = b.emit(mono[i].as_ref().expect("a value is built or a product"));
        built[i] = Some(v);
        v
    }
    for (i, op) in ops.iter().enumerate() {
        if let Op::Jet("scalar_multiply", a, _) = op {
            let mut m = Mono::constant(K::ONE);
            for x in a {
                let x = x.index();
                let f = match (&mono[x], scalar_const(&ops[x])) {
                    (Some(mx), _) => mx.clone(),
                    (None, Some(c)) => Mono::constant(c),
                    (None, None) => Mono::atom(get(&mut b, &mut built, &mono, x)),
                };
                m = m.times(&f);
            }
            mono[i] = Some(m);
            continue;
        }
        let args: Vec<Val> = op.args().iter().map(|a| get(&mut b, &mut built, &mono, a.index())).collect();
        built[i] = Some(b.push(op.with_args(&args)));
    }
    b.out
}

/// Drop operations nobody needs: an operation is needed if it is a check, an unwrap, a
/// witness, or an argument of a needed one.
fn dce(p: &Prog) -> Prog {
    let ops = p.ops();
    let mut need = vec![false; ops.len()];
    for i in (0..ops.len()).rev() {
        if matches!(ops[i], Op::Assert(_) | Op::Unwrap(..) | Op::Witness(..)) {
            need[i] = true;
        }
        if need[i] {
            for a in ops[i].args() {
                need[a.index()] = true;
            }
        }
    }
    let mut b = Builder::new();
    let mut map: Vec<Option<Val>> = vec![None; ops.len()];
    for (i, op) in ops.iter().enumerate() {
        if need[i] {
            let args: Vec<Val> = op.args().iter().map(|a| map[a.index()].expect("an argument before its reader")).collect();
            map[i] = Some(b.push(op.with_args(&args)));
        }
    }
    b.out
}

/// A value of the interpreter.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum V {
    S(K),
    B(bool),
    P(Box<V>, Box<V>),
}

/// Run the scalar subset of the IR (witness scalars, constants, the scalar jets, `eq_256`,
/// `scalar_is_zero`, `complement_1`, pairs, selections); the index of the first failing check.
#[cfg(test)]
pub(crate) fn eval(p: &Prog, wit: &HashMap<&str, K>) -> Result<Vec<Option<V>>, usize> {
    let mut v: Vec<Option<V>> = Vec::with_capacity(p.ops().len());
    let s = |v: &[Option<V>], a: &Val| match &v[a.index()] {
        Some(V::S(k)) => *k,
        other => panic!("not a scalar: {:?}", other),
    };
    for (i, op) in p.ops().iter().enumerate() {
        let x = match op {
            Op::Witness(n, _) => Some(V::S(wit[&**n])),
            Op::Const(Ty::Bit, b) => Some(V::B(b[0] & 1 == 1)),
            Op::Const(Ty::Word(256), b) => Some(scalar_const(op).map(V::S).unwrap_or_else(|| panic!("a non-canonical constant {:?}", b))),
            Op::Jet("scalar_add", a, _) => Some(V::S(s(&v, &a[0]) + s(&v, &a[1]))),
            Op::Jet("scalar_multiply", a, _) => Some(V::S(s(&v, &a[0]) * s(&v, &a[1]))),
            Op::Jet("scalar_negate", a, _) => Some(V::S(-s(&v, &a[0]))),
            Op::Jet("scalar_invert", a, _) => Some(V::S(Option::from(s(&v, &a[0]).invert()).unwrap_or(K::ZERO))),
            Op::Jet("eq_256", a, _) => Some(V::B(s(&v, &a[0]) == s(&v, &a[1]))),
            Op::Jet("scalar_is_zero", a, _) => Some(V::B(bool::from(s(&v, &a[0]).is_zero()))),
            Op::Jet("complement_1", a, _) => match &v[a[0].index()] {
                Some(V::B(b)) => Some(V::B(!b)),
                o => panic!("not a bit: {:?}", o),
            },
            Op::Pair(a, b, _) => Some(V::P(Box::new(v[a.index()].clone().unwrap()), Box::new(v[b.index()].clone().unwrap()))),
            Op::Fst(a, _) | Op::Snd(a, _) => match v[a.index()].clone() {
                Some(V::P(l, r)) => Some(if matches!(op, Op::Fst(..)) { *l } else { *r }),
                o => panic!("not a pair: {:?}", o),
            },
            Op::Select(c, a, b, _) => match &v[c.index()] {
                Some(V::B(true)) => v[a.index()].clone(),
                Some(V::B(false)) => v[b.index()].clone(),
                o => panic!("not a bit: {:?}", o),
            },
            Op::Assert(a) => match &v[a.index()] {
                Some(V::B(true)) => None,
                _ => return Err(i),
            },
            other => panic!("not interpreted: {:?}", other),
        };
        v.push(x);
    }
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::run::{dummy_env, execute_term, word_value};
    use std::collections::HashMap;
    use std::sync::Arc;

    fn be(s: &K) -> Vec<u8> {
        s.to_repr().to_vec()
    }
    fn mul(p: &mut Prog, a: Val, b: Val) -> Val {
        p.push(Op::Jet("scalar_multiply", vec![a, b], Ty::word()))
    }
    fn check(p: &mut Prog, v: Val, e: K) {
        let k = p.push(Op::Const(Ty::word(), be(&e)));
        let q = p.push(Op::Jet("eq_256", vec![v, k], Ty::Bit));
        p.push(Op::Assert(q));
    }
    /// The longest chain of `scalar_multiply` ending at each value.
    fn mul_depth(p: &Prog) -> Vec<usize> {
        let mut d = vec![0usize; p.ops().len()];
        for (i, o) in p.ops().iter().enumerate() {
            let m = o.args().iter().map(|a| d[a.index()]).max().unwrap_or(0);
            d[i] = m + matches!(o, Op::Jet("scalar_multiply", ..)) as usize;
        }
        d
    }
    fn count(p: &Prog, name: &str) -> usize {
        p.ops().iter().filter(|o| matches!(o, Op::Jet(n, ..) if *n == name)).count()
    }

    /// `mu^t` for t = 1..64 by a chain (as `util::powers`): checked values, at most one new
    /// product per power plus the squares, and depth O(log t).
    #[test]
    fn powers_become_products_of_squares() {
        let mu = K::from(7u64);
        let mut p = Prog::new();
        let w = p.push(Op::Witness("mu".into(), Ty::word()));
        let (mut x, mut e) = (w, mu);
        let mut pows = vec![];
        for _ in 1..64 {
            x = mul(&mut p, x, w);
            e *= mu;
            pows.push((x, e));
        }
        for (v, e) in &pows {
            check(&mut p, *v, *e);
        }
        let q = optimize(&p);
        let wit = HashMap::from([("mu", mu)]);
        assert!(eval(&q, &wit).is_ok());
        assert!(count(&q, "scalar_multiply") <= 64 + 6, "{} products", count(&q, "scalar_multiply"));
        assert!(mul_depth(&q).iter().max().unwrap() <= &12);
        let mut wrong = wit.clone();
        wrong.insert("mu", K::from(8u64));
        assert!(eval(&q, &wrong).is_err());
    }

    /// The WNLA tensor: t_i = prod_r (bit r of i ? gamma_r : rho_r).
    #[test]
    fn tensor_values_are_kept() {
        let names = ["g0", "g1", "g2", "g3", "r0", "r1", "r2", "r3"];
        let vals: Vec<K> = (0..8).map(|i| K::from(3 + 2 * i as u64)).collect();
        let mut p = Prog::new();
        let w: Vec<Val> = names.iter().map(|n| p.push(Op::Witness((*n).into(), Ty::word()))).collect();
        let one = p.push(Op::Const(Ty::word(), be(&K::ONE)));
        let mut t = vec![(one, K::ONE)];
        for r in 0..4 {
            let hi: Vec<(Val, K)> = t.iter().map(|(v, e)| (mul(&mut p, *v, w[r]), *e * vals[r])).collect();
            for x in t.iter_mut() {
                *x = (mul(&mut p, x.0, w[4 + r]), x.1 * vals[4 + r]);
            }
            t.extend(hi);
        }
        for (v, e) in &t {
            check(&mut p, *v, *e);
        }
        let q = optimize(&p);
        let wit: HashMap<&str, K> = names.iter().copied().zip(vals.iter().copied()).collect();
        assert!(eval(&q, &wit).is_ok());
        assert!(eval(&p, &wit).is_ok(), "the interpreter agrees with k256 on the original");
    }

    /// Constant factors become one coefficient: (3 x)(5 x) = 15 x^2.
    #[test]
    fn constant_factors_fold() {
        let x = K::from(11u64);
        let mut p = Prog::new();
        let w = p.push(Op::Witness("x".into(), Ty::word()));
        let k3 = p.push(Op::Const(Ty::word(), be(&K::from(3u64))));
        let k5 = p.push(Op::Const(Ty::word(), be(&K::from(5u64))));
        let a = mul(&mut p, k3, w);
        let b = mul(&mut p, w, k5);
        let c = mul(&mut p, a, b);
        check(&mut p, c, K::from(15u64) * x * x);
        let q = optimize(&p);
        assert!(eval(&q, &HashMap::from([("x", x)])).is_ok());
        assert_eq!(count(&q, "scalar_multiply"), 2, "x^2, then the coefficient");
    }

    /// A constant that is not a canonical scalar stays an atom (its bytes are kept).
    #[test]
    fn noncanonical_constant_stays_an_atom() {
        let mut p = Prog::new();
        let w = p.push(Op::Witness("x".into(), Ty::word()));
        let k = p.push(Op::Const(Ty::word(), vec![0xff; 32]));
        let m = mul(&mut p, w, k);
        let z = p.push(Op::Jet("scalar_is_zero", vec![m], Ty::Bit));
        let nz = p.push(Op::Jet("complement_1", vec![z], Ty::Bit));
        p.push(Op::Assert(nz));
        let q = optimize(&p);
        assert!(q.ops().iter().any(|o| matches!(o, Op::Const(_, b) if *b == vec![0xffu8; 32])));
    }

    /// Dead code goes; checks, unwraps read by nobody and witnesses stay.
    #[test]
    fn dce_keeps_effects_and_witnesses() {
        let build = |unread_witness: bool| {
            let mut p = Prog::new();
            let w = p.push(Op::Witness("x".into(), Ty::word()));
            if unread_witness {
                p.push(Op::Witness("y".into(), Ty::word()));
            }
            let _dead = mul(&mut p, w, w);
            let bit = p.push(Op::Const(Ty::Bit, vec![0]));
            let xv = p.push(Op::Const(Ty::word(), vec![0; 32]));
            let opt = p.push(Op::Jet("decompress", vec![bit, xv], Ty::opt(Ty::ge())));
            p.push(Op::Unwrap(opt, Ty::ge()));
            check(&mut p, w, K::from(2u64));
            p
        };
        let q = optimize(&build(true));
        assert_eq!(count(&q, "scalar_multiply"), 0);
        assert_eq!(q.ops().iter().filter(|o| matches!(o, Op::Witness(..))).count(), 2);
        assert_eq!(q.ops().iter().filter(|o| matches!(o, Op::Unwrap(..))).count(), 1);
        // run without the unread witness: rust-simplicity 0.9 panics when pruning a program whose
        // step computes and discards a witness (never generated by `compile`, where every witness
        // is checked)
        let q = optimize(&build(false));
        let w = HashMap::from([(Arc::<str>::from("x"), word_value(&be(&K::from(2u64))))]);
        assert!(execute_term(&q.to_term(), &w, &dummy_env(), false).is_err(), "the unwrap of x = 0 still fails");
    }

    /// Random programs: the optimized program accepts, and every check still runs.
    #[test]
    fn random_programs_keep_their_meaning() {
        use crate::simplicity::ir::random_programs::build;
        for seed in 1..40u64 {
            for n in [5usize, 20, 60] {
                let (p, w, checks) = build(seed, n, None);
                let q = optimize(&p);
                assert!(execute_term(&q.to_term(), &w, &dummy_env(), false).is_ok(), "seed {} n {}", seed, n);
                for c in 0..checks {
                    let (p, w, _) = build(seed, n, Some(c));
                    assert!(execute_term(&optimize(&p).to_term(), &w, &dummy_env(), false).is_err(), "seed {} n {} check {}", seed, n, c);
                }
            }
        }
    }
}

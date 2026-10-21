//! Rewrites of the IR that keep its meaning and make it cheaper to recompute: products as
//! products of squares of their atoms (shared prefixes), sums as balanced trees, common
//! subexpressions merged, dead code dropped. Exact: the scalar jets are arithmetic in F_n.

use std::collections::{BTreeMap, HashMap};

use k256::elliptic_curve::ff::PrimeField as _;

use crate::simplicity::ir::{Op, Prog, Ty, Val};

type K = k256::Scalar;

/// The rewrites, in order.
pub(crate) fn optimize(p: &Prog) -> Prog {
    dce(&reassociate(&monomials(p)))
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
    /// The product; none if an exponent would pass `u64` (the product then stays as it is).
    fn times(&self, o: &Mono) -> Option<Mono> {
        let mut f = self.f.clone();
        for (a, e) in &o.f {
            let x = f.entry(*a).or_insert(0);
            *x = x.checked_add(*e)?;
        }
        Some(Mono { c: self.c * o.c, f })
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
    /// Whether `v` is the result of a scalar jet (reduced mod n).
    fn canonical(&self, v: Val) -> bool {
        matches!(self.out.ops()[v.index()], Op::Jet("scalar_add" | "scalar_multiply" | "scalar_negate" | "scalar_invert" | "scalar_normalize", ..))
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
            // a lone atom is the product only if it is a canonical scalar already (the jet
            // reduces mod n: a witness word or a hash may be above n)
            Some(x) if m.c == K::ONE && (m.f.len() > 1 || m.f.values().any(|e| *e > 1) || self.canonical(x)) => x,
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
            let mut m = Some(Mono::constant(K::ONE));
            for x in a {
                let x = x.index();
                let f = match (&mono[x], scalar_const(&ops[x])) {
                    (Some(mx), _) => mx.clone(),
                    (None, Some(c)) => Mono::constant(c),
                    (None, None) => Mono::atom(get(&mut b, &mut built, &mono, x)),
                };
                m = m.and_then(|m| m.times(&f));
            }
            if m.is_some() {
                mono[i] = m;
                continue;
            }
            // an exponent past u64: built as it is, an atom for the products that read it
        }
        let args: Vec<Val> = op.args().iter().map(|a| get(&mut b, &mut built, &mono, a.index())).collect();
        built[i] = Some(b.push(op.with_args(&args)));
    }
    b.out
}

/// Chains of `scalar_add` whose partial sums are read once, by the next addition, as
/// balanced trees of their terms (in the order of the chain).
fn reassociate(p: &Prog) -> Prog {
    let ops = p.ops();
    let n = ops.len();
    let mut uses = vec![0usize; n];
    let mut reader = vec![usize::MAX; n];
    for (i, o) in ops.iter().enumerate() {
        for a in o.args() {
            uses[a.index()] += 1;
            reader[a.index()] = i;
        }
    }
    let is_add = |i: usize| matches!(ops[i], Op::Jet("scalar_add", ..));
    // a partial sum read once, by an addition: a part of its reader's chain, never built
    let absorbed: Vec<bool> = (0..n).map(|i| is_add(i) && uses[i] == 1 && is_add(reader[i])).collect();
    let mut b = Builder::new();
    let mut map: Vec<Option<Val>> = vec![None; n];
    for (i, op) in ops.iter().enumerate() {
        if absorbed[i] {
            continue;
        }
        if is_add(i) {
            // the chain's terms, left to right, without recursion (chains are long)
            let mut terms = Vec::new();
            let mut stack = vec![i];
            while let Some(j) = stack.pop() {
                if j != i && !absorbed[j] {
                    terms.push(map[j].expect("a term before its sum"));
                    continue;
                }
                let a = ops[j].args();
                // right argument pushed first: the left one is visited first
                stack.push(a[1].index());
                stack.push(a[0].index());
            }
            map[i] = Some(balanced_sum(&mut b, &terms));
            continue;
        }
        let args: Vec<Val> = op.args().iter().map(|a| map[a.index()].expect("an argument before its reader")).collect();
        map[i] = Some(b.push(op.with_args(&args)));
    }
    b.out
}

fn balanced_sum(b: &mut Builder, terms: &[Val]) -> Val {
    if terms.len() == 1 {
        return terms[0];
    }
    let h = terms.len() / 2;
    let l = balanced_sum(b, &terms[..h]);
    let r = balanced_sum(b, &terms[h..]);
    b.add(l, r)
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

    /// The longest chain of `scalar_add` ending at each value.
    fn add_depth(p: &Prog) -> Vec<usize> {
        let mut d = vec![0usize; p.ops().len()];
        for (i, o) in p.ops().iter().enumerate() {
            let m = o.args().iter().map(|a| d[a.index()]).max().unwrap_or(0);
            d[i] = m + matches!(o, Op::Jet("scalar_add", ..)) as usize;
        }
        d
    }

    /// A sum of 100 witnesses by a chain becomes a balanced tree (depth 7) of the same value.
    #[test]
    fn add_chain_becomes_balanced() {
        let mut p = Prog::new();
        let mut wit = HashMap::new();
        let names: Vec<String> = (0..100).map(|i| format!("w{}", i)).collect();
        let mut acc = None;
        let mut sum = K::ZERO;
        for (i, n) in names.iter().enumerate() {
            let v = p.push(Op::Witness(n.as_str().into(), Ty::word()));
            let k = K::from(i as u64 + 1);
            sum += k;
            acc = Some(match acc {
                None => v,
                Some(a) => p.push(Op::Jet("scalar_add", vec![a, v], Ty::word())),
            });
        }
        for (i, n) in names.iter().enumerate() {
            wit.insert(n.as_str(), K::from(i as u64 + 1));
        }
        check(&mut p, acc.unwrap(), sum);
        let q = optimize(&p);
        assert!(eval(&q, &wit).is_ok());
        assert_eq!(*add_depth(&q).iter().max().unwrap(), 7);
    }

    /// A partial sum read twice ends one chain and is a term of another.
    #[test]
    fn shared_partial_sum_is_kept() {
        let mut p = Prog::new();
        let w: Vec<Val> = (0..6).map(|i| p.push(Op::Witness(format!("w{}", i).as_str().into(), Ty::word()))).collect();
        let a = p.push(Op::Jet("scalar_add", vec![w[0], w[1]], Ty::word()));
        let b = p.push(Op::Jet("scalar_add", vec![a, w[2]], Ty::word())); // read twice
        let c = p.push(Op::Jet("scalar_add", vec![b, w[3]], Ty::word()));
        let d = p.push(Op::Jet("scalar_add", vec![b, w[4]], Ty::word()));
        let e = p.push(Op::Jet("scalar_add", vec![c, d], Ty::word()));
        let wit: HashMap<&str, K> = (0..6).map(|i| (["w0", "w1", "w2", "w3", "w4", "w5"][i], K::from(i as u64 + 1))).collect();
        let s = |i: usize| K::from(i as u64 + 1);
        check(&mut p, e, (s(0) + s(1) + s(2)) * K::from(2u64) + s(3) + s(4));
        check(&mut p, b, s(0) + s(1) + s(2));
        assert!(eval(&optimize(&p), &wit).is_ok());
    }

    /// 20 000 terms: no stack overflow in the passes, depth 15.
    #[test]
    fn long_add_chain_is_flattened_iteratively() {
        let mut p = Prog::new();
        let w = p.push(Op::Witness("x".into(), Ty::word()));
        let mut acc = w;
        for _ in 1..20_000 {
            acc = p.push(Op::Jet("scalar_add", vec![acc, w], Ty::word()));
        }
        check(&mut p, acc, K::from(20_000u64) * K::from(3u64));
        let q = optimize(&p);
        assert!(eval(&q, &HashMap::from([("x", K::from(3u64))])).is_ok());
        assert_eq!(*add_depth(&q).iter().max().unwrap(), 15);
    }

    /// The same program optimizes to the same operations.
    #[test]
    fn optimize_is_deterministic() {
        use crate::simplicity::ir::random_programs::build;
        for seed in 1..10u64 {
            let (p, _, _) = build(seed, 60, None);
            assert_eq!(format!("{:?}", optimize(&p).ops()), format!("{:?}", optimize(&p).ops()));
        }
    }

    /// x · 1 of a word that is not a canonical scalar is reduced by the jet: the rewrite must
    /// keep the product, not return x (review, stage 3).
    #[test]
    fn noncanonical_atom_times_one_keeps_the_reduction() {
        // n + 5
        let n5 = {
            let mut b = [0u8; 32];
            b.copy_from_slice(&(0..64).step_by(2).map(|i| u8::from_str_radix(&"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364146"[i..i + 2], 16).unwrap()).collect::<Vec<u8>>());
            b
        };
        let build = |expected: &[u8]| {
            let mut p = Prog::new();
            let w = p.push(Op::Witness("x".into(), Ty::word()));
            let one = p.push(Op::Const(Ty::word(), be(&K::ONE)));
            let m = mul(&mut p, w, one);
            let k = p.push(Op::Const(Ty::word(), expected.to_vec()));
            let q = p.push(Op::Jet("eq_256", vec![m, k], Ty::Bit));
            p.push(Op::Assert(q));
            p
        };
        let w = HashMap::from([(Arc::<str>::from("x"), word_value(&n5))]);
        let run = |p: &Prog| execute_term(&p.to_term(), &w, &dummy_env(), false).is_ok();
        let five = be(&K::from(5u64));
        assert!(run(&build(&five)), "the jet reduces n + 5 to 5");
        assert!(run(&optimize(&build(&five))));
        assert!(!run(&build(&n5)));
        assert!(!run(&optimize(&build(&n5))));
    }

    /// An exponent past u64 (64 squarings of a square) keeps its value.
    #[test]
    fn exponent_overflow_keeps_the_value() {
        let x = K::from(3u64);
        let mut p = Prog::new();
        let w = p.push(Op::Witness("x".into(), Ty::word()));
        let (mut s, mut e) = (w, x);
        for _ in 0..65 {
            s = mul(&mut p, s, s);
            e = e * e;
        }
        check(&mut p, s, e);
        let wit = HashMap::from([("x", x)]);
        assert!(eval(&p, &wit).is_ok());
        assert!(eval(&optimize(&p), &wit).is_ok());
    }
}

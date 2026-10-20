//! A small SSA language over Simplicity values, and its lowering to Simplicity's human-readable
//! encoding.
//!
//! A program is a list of operations; each defines a value from earlier ones. The lowering runs
//! them as a chain of steps over an environment holding the values still needed (liveness):
//! step `k` computes its value from the environment and rebuilds it as a right-nested list
//! `(v_1, (v_2, ... (v_m, 1)))`, ordered by value number. Constants and witnesses used once are
//! read where they are used, never stored (a witness node may be reached by one path only).

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::sync::Arc;

/// The type of a value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Ty {
    /// One bit, `2 = 1 + 1`.
    Bit,
    /// A word of `2^k` bits, `k ≥ 3` (bytes, `u64`, 256-bit scalars, field elements, hashes).
    Word(u32),
    /// A pair.
    Prod(Box<Ty>, Box<Ty>),
    /// An option, `1 + T`.
    Opt(Box<Ty>),
    /// A SHA-256 context of the `sha_256_ctx_8_*` jets (only ever produced by jets: its type is
    /// inferred, never written).
    Ctx,
}

impl Ty {
    /// A 256-bit word.
    pub(crate) fn word() -> Ty {
        Ty::Word(256)
    }
    /// `(a, b)`.
    pub(crate) fn prod(a: Ty, b: Ty) -> Ty {
        Ty::Prod(Box::new(a), Box::new(b))
    }
    /// `1 + t`.
    pub(crate) fn opt(t: Ty) -> Ty {
        Ty::Opt(Box::new(t))
    }
    /// An affine point `(x, y)`.
    pub(crate) fn ge() -> Ty {
        Ty::prod(Ty::word(), Ty::word())
    }
    /// A Jacobian point `((x, y), z)`.
    pub(crate) fn gej() -> Ty {
        Ty::prod(Ty::ge(), Ty::word())
    }

    /// The type in the human-readable encoding (`None` for a context: left to inference).
    fn text(&self) -> Option<String> {
        Some(match self {
            Ty::Bit => "2".into(),
            Ty::Word(n) => format!("2^{}", n),
            Ty::Prod(a, b) => format!("({} * {})", a.text()?, b.text()?),
            Ty::Opt(t) => format!("(1 + {})", t.text()?),
            Ty::Ctx => return None,
        })
    }

    /// The bytes a constant of this type takes (a bit takes one byte, 0 or 1).
    fn const_bytes(&self) -> usize {
        match self {
            Ty::Bit => 1,
            Ty::Word(n) => (*n as usize) / 8,
            Ty::Prod(a, b) => a.const_bytes() + b.const_bytes(),
            Ty::Opt(_) | Ty::Ctx => panic!("no constants of this type"),
        }
    }
}

/// A value: the result of an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Val(u32);

/// An operation.
#[derive(Clone, Debug)]
pub(crate) enum Op {
    /// A constant: big-endian bytes, laid out as the type (a pair is its halves' bytes, a bit one
    /// byte 0 or 1).
    Const(Ty, Vec<u8>),
    /// A named witness value.
    Witness(Arc<str>, Ty),
    /// A jet (name without `jet_`) applied to its arguments, paired right-nested
    /// (`[a, b, c]` is `(a, (b, c))`), with its result type.
    Jet(&'static str, Vec<Val>, Ty),
    /// The value of an option that must be some; fails on none.
    Unwrap(Val, Ty),
    /// A pair.
    Pair(Val, Val, Ty),
    /// The first half of a pair.
    Fst(Val, Ty),
    /// The second half of a pair.
    Snd(Val, Ty),
    /// `bit ? a : b`.
    Select(Val, Val, Val, Ty),
    /// A bit that must be 1.
    Assert(Val),
}

impl Op {
    fn args(&self) -> Vec<Val> {
        match self {
            Op::Const(..) | Op::Witness(..) => vec![],
            Op::Jet(_, a, _) => a.clone(),
            Op::Unwrap(v, _) | Op::Fst(v, _) | Op::Snd(v, _) | Op::Assert(v) => vec![*v],
            Op::Pair(a, b, _) => vec![*a, *b],
            Op::Select(c, a, b, _) => vec![*c, *a, *b],
        }
    }

    fn ty(&self) -> Option<Ty> {
        match self {
            Op::Const(t, _) | Op::Witness(_, t) | Op::Jet(_, _, t) | Op::Unwrap(_, t) | Op::Pair(_, _, t) => Some(t.clone()),
            Op::Fst(_, t) | Op::Snd(_, t) | Op::Select(_, _, _, t) => Some(t.clone()),
            Op::Assert(_) => None,
        }
    }
}

/// A program: operations in order.
#[derive(Clone, Debug, Default)]
pub(crate) struct Prog {
    ops: Vec<Op>,
    tys: Vec<Option<Ty>>,
}

impl Prog {
    /// An empty program.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Append an operation; its value (meaningless for an assertion).
    pub(crate) fn push(&mut self, op: Op) -> Val {
        for a in op.args() {
            assert!((a.0 as usize) < self.ops.len(), "an argument from the future");
            assert!(self.tys[a.0 as usize].is_some(), "an assertion has no value");
        }
        if let Op::Const(t, b) = &op {
            assert_eq!(t.const_bytes(), b.len(), "a constant's bytes do not match its type");
        }
        if let Op::Witness(name, _) = &op {
            assert!(!self.ops.iter().any(|o| matches!(o, Op::Witness(n, _) if n == name)), "a witness name used twice");
        }
        let v = Val(self.ops.len() as u32);
        self.tys.push(op.ty());
        self.ops.push(op);
        v
    }

    /// The type of a value.
    pub(crate) fn ty(&self, v: Val) -> &Ty {
        self.tys[v.0 as usize].as_ref().expect("an assertion has no value")
    }

    /// The witness names and types, in program order.
    pub(crate) fn witness_types(&self) -> Vec<(Arc<str>, Ty)> {
        self.ops.iter().filter_map(|o| if let Op::Witness(n, t) = o { Some((n.clone(), t.clone())) } else { None }).collect()
    }

    /// Jets by name: how many times the program calls each.
    pub(crate) fn stats(&self) -> BTreeMap<&'static str, usize> {
        let mut m = BTreeMap::new();
        for o in &self.ops {
            match o {
                Op::Jet(n, _, _) => *m.entry(*n).or_insert(0) += 1,
                Op::Assert(_) => *m.entry("verify").or_insert(0) += 1,
                _ => {}
            }
        }
        m
    }

    /// The program in the human-readable encoding, with `main`.
    pub(crate) fn to_text(&self) -> String {
        Lowering::new(self).run()
    }
}

/// How an operation's value is reached.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// A definition read where used (constants; witnesses used once).
    Inline,
    /// Stored in the environment from its step to its last use.
    Stored,
}

struct Lowering<'a> {
    p: &'a Prog,
    kind: Vec<Kind>,
    last_use: Vec<usize>,
    out: String,
    consts: HashMap<(Ty, Vec<u8>), String>,
}

impl<'a> Lowering<'a> {
    fn new(p: &'a Prog) -> Self {
        let n = p.ops.len();
        let mut uses = vec![0usize; n];
        let mut last_use = vec![0usize; n];
        for (i, o) in p.ops.iter().enumerate() {
            for a in o.args() {
                uses[a.0 as usize] += 1;
                last_use[a.0 as usize] = i;
            }
        }
        let kind = p
            .ops
            .iter()
            .enumerate()
            .map(|(i, o)| match o {
                Op::Const(..) => Kind::Inline,
                Op::Witness(..) if uses[i] <= 1 => Kind::Inline,
                _ => Kind::Stored,
            })
            .collect();
        Lowering { p, kind, last_use, out: String::new(), consts: HashMap::new() }
    }

    /// The name of a constant's definition (emitted once).
    fn constant(&mut self, t: &Ty, bytes: &[u8]) -> String {
        if let Some(n) = self.consts.get(&(t.clone(), bytes.to_vec())) {
            return n.clone();
        }
        // a definition is one node with one type: the constant itself (1 -> T) is shared, the
        // `comp unit` that reads it from any environment is per use
        let name = format!("k{}", self.consts.len());
        let expr = const_expr(t, bytes);
        let _ = writeln!(self.out, "{} := {}", name, expr);
        let read = format!("(comp unit {})", name);
        self.consts.insert((t.clone(), bytes.to_vec()), read.clone());
        read
    }

    /// The expression for value `v` given the environment `env` (stored values, in order).
    fn read(&mut self, v: Val, env: &[Val]) -> String {
        let i = v.0 as usize;
        match (&self.p.ops[i], self.kind[i]) {
            (Op::Const(t, b), _) => {
                let (t, b) = (t.clone(), b.clone());
                self.constant(&t, &b)
            }
            (Op::Witness(name, _), Kind::Inline) => name.to_string(),
            _ => {
                // paths are written out: a shared definition would have one type for every
                // environment it is used in
                let pos = env.iter().position(|x| *x == v).expect("a value read after it was dropped");
                let mut path = String::from("(take iden)");
                for _ in 0..pos {
                    path = format!("(drop {})", path);
                }
                path
            }
        }
    }

    /// The expression computing op `i`'s value from `env`.
    fn expr(&mut self, i: usize, env: &[Val]) -> String {
        let op = self.p.ops[i].clone();
        match op {
            Op::Const(..) => unreachable!("constants are inline"),
            Op::Witness(name, _) => name.to_string(),
            Op::Jet(name, args, _) => {
                if args.is_empty() {
                    return format!("comp unit jet_{}", name);
                }
                let tuple = self.tuple(&args, env);
                format!("comp ({}) jet_{}", tuple, name)
            }
            Op::Unwrap(v, _) => {
                let x = self.read(v, env);
                format!("comp (pair {} unit) (assertr #{{unit}} (take iden))", x)
            }
            Op::Pair(a, b, _) => {
                let (x, y) = (self.read(a, env), self.read(b, env));
                format!("pair {} {}", x, y)
            }
            Op::Fst(v, _) => format!("comp {} (take iden)", self.read(v, env)),
            Op::Snd(v, _) => format!("comp {} (drop iden)", self.read(v, env)),
            Op::Select(c, a, b, _) => {
                let (bit, x, y) = (self.read(c, env), self.read(a, env), self.read(b, env));
                format!("comp (pair {} iden) (case (drop {}) (drop {}))", bit, y, x)
            }
            Op::Assert(_) => unreachable!("assertions are steps of their own"),
        }
    }

    /// Arguments paired right-nested.
    fn tuple(&mut self, args: &[Val], env: &[Val]) -> String {
        let first = self.read(args[0], env);
        if args.len() == 1 {
            first
        } else {
            format!("pair {} ({})", first, self.tuple(&args[1..], env))
        }
    }

    /// `(e_1, (e_2, ... (e_m, unit)))` for the environment `next`, where `fresh` (if any) is
    /// computed by `fresh_expr` and the others are read from `env`.
    fn rebuild(&mut self, next: &[Val], env: &[Val], fresh: Option<(Val, String)>) -> String {
        let mut s = String::from("unit");
        for v in next.iter().rev() {
            let e = match &fresh {
                Some((f, e)) if f == v => e.clone(),
                _ => self.read(*v, env),
            };
            s = format!("pair ({}) ({})", e, s);
        }
        s
    }

    fn run(mut self) -> String {
        for (name, t) in self.p.witness_types() {
            let _ = writeln!(self.out, "{} := witness : _ -> {}", name, t.text().expect("witness types are written"));
        }
        let mut env: Vec<Val> = Vec::new();
        let mut steps = Vec::new();
        for i in 0..self.p.ops.len() {
            if self.kind[i] == Kind::Inline {
                continue;
            }
            let v = Val(i as u32);
            // live after this step: stored values defined so far whose last use is later
            let mut next: Vec<Val> = env.iter().copied().filter(|x| self.last_use[x.0 as usize] > i).collect();
            let step = match &self.p.ops[i] {
                Op::Assert(b) => {
                    let bit = self.read(*b, &env);
                    let rest = self.rebuild(&next, &env, None);
                    format!("comp (pair (comp ({}) jet_verify) ({})) (drop iden)", bit, rest)
                }
                _ => {
                    let e = self.expr(i, &env);
                    if self.last_use[i] > i {
                        next.push(v);
                        next.sort();
                    }
                    let fresh = Some((v, e.clone()));
                    if next.contains(&v) {
                        self.rebuild(&next, &env, fresh)
                    } else {
                        // a value nobody reads (e.g. a final check written as a jet): computed
                        // and discarded
                        format!("comp (pair ({}) ({})) (drop iden)", e, self.rebuild(&next, &env, None))
                    }
                }
            };
            let name = format!("st{}", steps.len());
            let _ = writeln!(self.out, "{} := {}", name, step);
            steps.push(name);
            env = next;
        }
        let mut main = String::from("unit");
        for s in steps.iter().rev() {
            main = format!("comp {} ({})", s, main);
        }
        format!("{}main := {}\n", self.out, main)
    }
}

/// A constant of type `t` from its bytes.
fn const_expr(t: &Ty, bytes: &[u8]) -> String {
    match t {
        Ty::Bit => format!("const 0b{}", bytes[0] & 1),
        Ty::Word(_) => {
            let mut s = String::from("const 0x");
            for b in bytes {
                let _ = write!(s, "{:02x}", b);
            }
            s
        }
        Ty::Prod(a, b) => {
            let n = a.const_bytes();
            format!("pair ({}) ({})", const_expr(a, &bytes[..n]), const_expr(b, &bytes[n..]))
        }
        Ty::Opt(_) | Ty::Ctx => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::run::{dummy_env, execute_text_unbudgeted as execute_text, word_value};
    use k256::elliptic_curve::ff::PrimeField as _;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn be(s: &k256::Scalar) -> Vec<u8> {
        s.to_repr().to_vec()
    }

    fn sc(x: u64) -> k256::Scalar {
        k256::Scalar::from(x)
    }

    /// `inv(a b + c)` from witnesses, checked against k256.
    fn arithmetic(c_off: u64) -> Result<crate::simplicity::run::Report, crate::simplicity::run::ExecError> {
        let (a, b, c) = (sc(11), sc(13), sc(17));
        let expected = (a * b + c).invert().unwrap();
        let mut p = Prog::new();
        let wa = p.push(Op::Witness("a".into(), Ty::word()));
        let wb = p.push(Op::Witness("b".into(), Ty::word()));
        let wc = p.push(Op::Witness("c".into(), Ty::word()));
        let m = p.push(Op::Jet("scalar_multiply", vec![wa, wb], Ty::word()));
        let s = p.push(Op::Jet("scalar_add", vec![m, wc], Ty::word()));
        let i = p.push(Op::Jet("scalar_invert", vec![s], Ty::word()));
        let k = p.push(Op::Const(Ty::word(), be(&expected)));
        let e = p.push(Op::Jet("eq_256", vec![i, k], Ty::Bit));
        p.push(Op::Assert(e));
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("a"), word_value(&be(&a)));
        w.insert(Arc::<str>::from("b"), word_value(&be(&b)));
        w.insert(Arc::<str>::from("c"), word_value(&be(&(c + sc(c_off)))));
        execute_text(&p.to_text(), &w, &dummy_env())
    }

    #[test]
    fn scalar_arithmetic_runs_as_a_node() {
        assert!(arithmetic(0).is_ok(), "{:?}", arithmetic(0).err());
        assert!(arithmetic(1).is_err());
    }

    /// A value defined first and used last, with 39 unrelated steps between.
    #[test]
    fn values_live_across_many_steps() {
        let (a, b, c) = (sc(2), sc(3), sc(5));
        let mut p = Prog::new();
        let wa = p.push(Op::Witness("a".into(), Ty::word()));
        let wb = p.push(Op::Witness("b".into(), Ty::word()));
        let wc = p.push(Op::Witness("c".into(), Ty::word()));
        let v1 = p.push(Op::Jet("scalar_add", vec![wa, wb], Ty::word()));
        let one = p.push(Op::Const(Ty::word(), be(&sc(1))));
        let mut t = wc;
        for _ in 0..39 {
            t = p.push(Op::Jet("scalar_add", vec![t, one], Ty::word()));
        }
        let r = p.push(Op::Jet("scalar_add", vec![v1, t], Ty::word()));
        let k = p.push(Op::Const(Ty::word(), be(&(a + b + c + sc(39)))));
        let e = p.push(Op::Jet("eq_256", vec![r, k], Ty::Bit));
        p.push(Op::Assert(e));
        let mut w = HashMap::new();
        for (n, v) in [("a", a), ("b", b), ("c", c)] {
            w.insert(Arc::<str>::from(n), word_value(&be(&v)));
        }
        let rep = execute_text(&p.to_text(), &w, &dummy_env()).unwrap();
        assert!(rep.cost_mwu > 0);
    }

    #[test]
    fn text_is_deterministic() {
        let build = || {
            let mut p = Prog::new();
            let wa = p.push(Op::Witness("a".into(), Ty::word()));
            let k = p.push(Op::Const(Ty::word(), be(&sc(7))));
            let m = p.push(Op::Jet("scalar_multiply", vec![wa, k], Ty::word()));
            let e = p.push(Op::Jet("eq_256", vec![m, k], Ty::Bit));
            p.push(Op::Assert(e));
            p.to_text()
        };
        assert_eq!(build(), build());
    }

    /// `decompress` of x = 0 is none (no point with x = 0 on secp256k1): unwrapping fails.
    #[test]
    fn unwrap_fails_on_none() {
        let gx = hex_literal("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
        let run = |x: Vec<u8>| {
            let mut p = Prog::new();
            let bit = p.push(Op::Const(Ty::Bit, vec![0]));
            let xv = p.push(Op::Const(Ty::word(), x.clone()));
            let opt = p.push(Op::Jet("decompress", vec![bit, xv], Ty::opt(Ty::ge())));
            let ge = p.push(Op::Unwrap(opt, Ty::ge()));
            let gx2 = p.push(Op::Fst(ge, Ty::word()));
            let e = p.push(Op::Jet("eq_256", vec![gx2, xv], Ty::Bit));
            p.push(Op::Assert(e));
            execute_text(&p.to_text(), &HashMap::new(), &dummy_env())
        };
        assert!(run(gx).is_ok());
        assert!(run(vec![0u8; 32]).is_err());
    }

    fn hex_literal(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }
}

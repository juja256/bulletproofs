//! A small SSA language over Simplicity values, and its lowering to Simplicity's human-readable
//! encoding.
//!
//! A program is a list of operations; each defines a value from earlier ones. The lowering runs
//! them as a chain of steps over an environment holding the values still needed (liveness):
//! step `k` computes its value from the environment and rebuilds it as a right-nested list
//! `(v_1, (v_2, ... (v_m, 1)))`, ordered by last use. Constants and witnesses used once are
//! read where they are used, never stored (a witness node may be reached by one path only).

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::simplicity::term::Term;

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
    /// The buffer of a SHA-256 context (inferred, never written).
    CtxBuf,
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

    /// The bytes a constant of this type takes (a bit takes one byte, 0 or 1).
    fn const_bytes(&self) -> usize {
        match self {
            Ty::Bit => 1,
            Ty::Word(n) => (*n as usize) / 8,
            Ty::Prod(a, b) => a.const_bytes() + b.const_bytes(),
            Ty::Opt(_) | Ty::Ctx | Ty::CtxBuf => panic!("no constants of this type"),
        }
    }
}

/// A value: the result of an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Val(u32);

impl Val {
    /// The position of the operation that defines it.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

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
    /// The arguments, in order.
    pub(crate) fn args(&self) -> Vec<Val> {
        match self {
            Op::Const(..) | Op::Witness(..) => vec![],
            Op::Jet(_, a, _) => a.clone(),
            Op::Unwrap(v, _) | Op::Fst(v, _) | Op::Snd(v, _) | Op::Assert(v) => vec![*v],
            Op::Pair(a, b, _) => vec![*a, *b],
            Op::Select(c, a, b, _) => vec![*c, *a, *b],
        }
    }

    /// The same operation on other arguments (in the order of [`Op::args`]).
    pub(crate) fn with_args(&self, a: &[Val]) -> Op {
        match self {
            Op::Const(..) | Op::Witness(..) => self.clone(),
            Op::Jet(n, _, t) => Op::Jet(n, a.to_vec(), t.clone()),
            Op::Unwrap(_, t) => Op::Unwrap(a[0], t.clone()),
            Op::Pair(_, _, t) => Op::Pair(a[0], a[1], t.clone()),
            Op::Fst(_, t) => Op::Fst(a[0], t.clone()),
            Op::Snd(_, t) => Op::Snd(a[0], t.clone()),
            Op::Select(_, _, _, t) => Op::Select(a[0], a[1], a[2], t.clone()),
            Op::Assert(_) => Op::Assert(a[0]),
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

    /// The operations in order.
    pub(crate) fn ops(&self) -> &[Op] {
        &self.ops
    }

    /// The type of a value.
    #[allow(dead_code)]
    pub(crate) fn ty(&self, v: Val) -> &Ty {
        self.tys[v.0 as usize].as_ref().expect("an assertion has no value")
    }

    /// The program as a DAG of combinators, and what it runs, with the lowering `opts`.
    pub(crate) fn lower(&self, opts: &Options) -> Lowered {
        let l = Lowering::new(self, opts);
        let mut jets = BTreeMap::new();
        for (i, o) in self.ops.iter().enumerate() {
            let times = if l.role[i] == Role::Root { 1 } else { l.exec[i] as usize };
            match o {
                Op::Jet(n, _, _) => *jets.entry(*n).or_insert(0) += times,
                Op::Assert(_) => *jets.entry("verify").or_insert(0) += 1,
                _ => {}
            }
        }
        let steps = l.steps();
        let stored = l.order.iter().filter(|&&r| !matches!(self.ops[r], Op::Assert(_)) && l.last_use[r] > l.pos[r]).count();
        let live_bits = l.live_bits;
        Lowered { term: l.run(), jets, steps, stored, live_bits }
    }

    /// Jets by name: how many times the program runs each (a recomputed value runs at each
    /// of its readers); `verify` once per check (default options).
    #[cfg(test)]
    pub(crate) fn stats(&self) -> BTreeMap<&'static str, usize> {
        self.lower(&Options::default()).jets
    }

    /// The program as a DAG of combinators (default options).
    #[cfg(test)]
    pub(crate) fn to_term(&self) -> Term {
        Lowering::new(self, &Options::default()).run()
    }

    /// The number of steps the program runs (values read several times or by nobody, checks).
    #[cfg(test)]
    pub(crate) fn step_count(&self) -> usize {
        Lowering::new(self, &Options::default()).steps()
    }

    /// Steps that store a value for later steps.
    #[cfg(test)]
    pub(crate) fn stored_count(&self) -> usize {
        self.lower(&Options::default()).stored
    }

    /// Diagnostic: stored values by operation, with their count, Σ bits × steps alive and Σ
    /// readers' executions.
    #[cfg(test)]
    pub(crate) fn stored_report(&self) -> BTreeMap<String, (usize, u64, u64)> {
        let l = Lowering::new(self, &Options::default());
        let mut m = BTreeMap::new();
        for &r in &l.order {
            if matches!(self.ops[r], Op::Assert(_)) || l.last_use[r] <= l.pos[r] {
                continue;
            }
            let name = match &self.ops[r] {
                Op::Jet(n, ..) => format!("jet {}", n),
                o => format!("{:?}", o).split('(').next().unwrap().to_string(),
            };
            let bits = self.tys[r].as_ref().map_or(0, bits_of);
            let e = m.entry(name).or_insert((0usize, 0u64, 0u64));
            e.0 += 1;
            e.1 += bits * (l.last_use[r] - l.pos[r]) as u64;
            e.2 += l.exec[r];
        }
        m
    }

    /// The scheduler's measure: Σ over steps of the bits live after the step.
    #[cfg(test)]
    pub(crate) fn live_bits(&self) -> u64 {
        Lowering::new(self, &Options::default()).live_bits
    }

    /// The program in the human-readable encoding (an artifact of [`Prog::to_term`]).
    #[cfg(test)]
    pub(crate) fn to_text(&self) -> String {
        self.to_term().text().expect("the program types")
    }

}

/// How an operation is lowered (expression trees).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    /// A constant, read where used.
    Const,
    /// A witness read once: the witness node at its reader.
    InlineWitness,
    /// A value read once (and not in a branch of a selection): built inside its reader's
    /// expression, so it is written once, straight into its reader's input.
    Inline,
    /// A step of its own: a value read several times (stored while it has readers left), a
    /// value read by nobody (computed and discarded: it may contain a check), an assertion.
    Root,
}

struct Lowering<'a> {
    p: &'a Prog,
    role: Vec<Role>,
    /// How many times each operation runs (a value recomputed at each reader runs at each).
    exec: Vec<u64>,
    /// The position of each root in `order`.
    pos: Vec<usize>,
    /// For a root, the last position (in `order`) that reads it (its own if none).
    last_use: Vec<usize>,
    /// The roots in the order they run.
    order: Vec<usize>,
    /// The scheduler's measure: Σ over steps of the live bits.
    live_bits: u64,
    /// The slot of each stored value (`usize::MAX` if none yet).
    slot: Vec<usize>,
    /// The value in each slot of the environment tree.
    occupant: Vec<Option<usize>>,
    /// The tree's height: `2^height` slots.
    height: usize,
    consts: HashMap<(Ty, Vec<u8>), Term>,
    witnesses: HashMap<Arc<str>, Term>,
    /// The expressions of inlined values built in the current step (they read its slots).
    cache: HashMap<usize, Term>,
}

impl<'a> Lowering<'a> {
    fn new(p: &'a Prog, opts: &Options) -> Self {
        let n = p.ops.len();
        // every reader, with multiplicity (mul(x, x) reads x twice)
        let mut readers: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut in_branch = vec![false; n];
        for (i, o) in p.ops.iter().enumerate() {
            for a in o.args() {
                readers[a.0 as usize].push(i);
            }
            // the arms of a selection run in one branch only: never inline into them (a check
            // there would run only when its branch is taken)
            if let Op::Select(_, x, y, _) = o {
                in_branch[x.0 as usize] = true;
                in_branch[y.0 as usize] = true;
            }
        }
        // Roles are decided, the roots scheduled, and then (`role_passes` > 1) decided again with
        // what the previous pass found: the arguments actually inlined and the steps that
        // actually run each value.
        let mut prev: Option<(Vec<Role>, Vec<usize>, Vec<usize>)> = None;
        let mut out = None;
        let passes = opts.role_passes.max(1);
        for pass in 0..passes {
            let (role, exec) = Self::decide(p, &readers, &in_branch, prev.as_ref().map(|(r, lo, hi)| (r.as_slice(), lo.as_slice(), hi.as_slice())));
            let sched = Self::schedule_roots(p, &role);
            if pass + 1 < passes {
                // the first and last step (position) running each value
                let (lo, hi) = Self::owner_span(p, &readers, &role, &sched.3);
                prev = Some((role.clone(), lo, hi));
            }
            out = Some((role, exec, sched));
        }
        let (role, exec, (roots, reads, live_bits, pos, order)) = out.expect("a pass");
        // a stored value lives until the last step whose expression reads it
        let mut last_use: Vec<usize> = (0..n).map(|i| pos[i]).collect();
        for (k, &r) in roots.iter().enumerate() {
            for &a in &reads[k] {
                last_use[a] = last_use[a].max(pos[r]);
            }
        }
        // the most values alive at once: the number of slots
        let mut deaths = vec![0usize; order.len() + 1];
        for &r in &order {
            if !matches!(p.ops[r], Op::Assert(_)) && last_use[r] > pos[r] {
                deaths[last_use[r]] += 1;
            }
        }
        let mut alive = 0usize;
        let mut most = 1usize;
        for (k, &r) in order.iter().enumerate() {
            alive -= deaths[k];
            if !matches!(p.ops[r], Op::Assert(_)) && last_use[r] > k {
                alive += 1;
            }
            most = most.max(alive);
        }
        let height = (usize::BITS - (most - 1).leading_zeros()) as usize;
        Lowering { p, role, exec, pos, last_use, order, live_bits, slot: vec![usize::MAX; n], occupant: vec![None; 1 << height], height, consts: HashMap::new(), witnesses: HashMap::new(), cache: HashMap::new() }
    }

    /// Roles from the last operation back: a value's readers are decided before it, so the
    /// times it runs are known. `prev`: the roles and the first and last step running each
    /// value, from a previous pass.
    fn decide(p: &Prog, readers: &[Vec<usize>], in_branch: &[bool], prev: Option<(&[Role], &[usize], &[usize])>) -> (Vec<Role>, Vec<u64>) {
        let n = p.ops.len();
        // what recomputing a value costs: itself and the arguments that run wherever it runs
        // (read only by it; or, after a pass, inlined)
        let mut tree_cost = vec![0u64; n];
        for i in 0..n {
            let own: u64 = p.ops[i]
                .args()
                .iter()
                .map(|a| a.0 as usize)
                .filter(|&a| !matches!(p.ops[a], Op::Const(..) | Op::Witness(..)))
                .filter(|&a| match prev {
                    Some((r, _, _)) => r[a] == Role::Inline,
                    None => readers[a].len() == 1,
                })
                .map(|a| tree_cost[a])
                .fold(0u64, |x, y| x.saturating_add(y));
            tree_cost[i] = local_cost(p, i).saturating_add(own);
        }
        let mut role = vec![Role::Root; n];
        let mut exec = vec![0u64; n];
        // the last root (in program order) that runs each value: itself if a root, else the
        // last root running one of its readers
        let mut last_owner: Vec<usize> = (0..n).collect();
        let mut roots_at = Fenwick::new(n);
        for i in (0..n).rev() {
            exec[i] = readers[i].iter().map(|&r| if role[r] == Role::Root { 1 } else { exec[r] }).fold(0u64, |a, b| a.saturating_add(b));
            let owner = readers[i].iter().map(|&r| if role[r] == Role::Root { r } else { last_owner[r] }).max();
            let ty = p.tys[i].clone();
            role[i] = match &p.ops[i] {
                Op::Const(..) => Role::Const,
                Op::Assert(_) => Role::Root,
                _ if readers[i].is_empty() || in_branch[i] => Role::Root,
                // a value read from a transcript state (a hash) is stored: inlined into a late
                // step, it would keep the state (838 bits) alive until then
                _ if !matches!(ty, Some(Ty::Ctx) | Some(Ty::CtxBuf)) && p.ops[i].args().iter().any(|a| matches!(p.tys[a.0 as usize], Some(Ty::Ctx) | Some(Ty::CtxBuf))) => Role::Root,
                Op::Witness(..) => {
                    if exec[i] == 1 {
                        Role::InlineWitness
                    } else {
                        Role::Root
                    }
                }
                _ if exec[i] == 1 => Role::Inline,
                // a transcript state is never recomputed
                _ if matches!(ty, Some(Ty::Ctx) | Some(Ty::CtxBuf)) => Role::Root,
                _ => {
                    let bits = ty.as_ref().map_or(0, bits_of);
                    // it lives until the last step that reads it, not its last reader's position
                    let last = owner.expect("readers");
                    let life = (roots_at.prefix(last + 1) - roots_at.prefix(i + 1)).max(1);
                    let store = (2 * bits * life).saturating_add(exec[i].saturating_mul(read_cost(bits)));
                    let recompute = exec[i].saturating_mul(tree_cost[i]);
                    if recompute > store {
                        Role::Root
                    } else {
                        Role::Inline
                    }
                }
            };
            if role[i] == Role::Root {
                roots_at.add(i);
            } else if let Some(o) = owner {
                last_owner[i] = o;
            }
        }
        (role, exec)
    }

    /// The roots, the stored values each root's expression reads, the scheduler's live bits,
    /// each root's position, and the roots in order.
    #[allow(clippy::type_complexity)]
    fn schedule_roots(p: &Prog, role: &[Role]) -> (Vec<usize>, Vec<Vec<usize>>, u64, Vec<usize>, Vec<usize>) {
        let n = p.ops.len();
        let roots: Vec<usize> = (0..n).filter(|i| role[*i] == Role::Root).collect();
        let mut index = vec![usize::MAX; n];
        for (k, r) in roots.iter().enumerate() {
            index[*r] = k;
        }
        // the stored values each root's expression reads, through its inlined arguments
        let mut stamp = vec![usize::MAX; n];
        let mut reads: Vec<Vec<usize>> = vec![Vec::new(); roots.len()];
        for (k, &r) in roots.iter().enumerate() {
            let mut stack: Vec<usize> = p.ops[r].args().iter().map(|a| a.0 as usize).collect();
            while let Some(a) = stack.pop() {
                if stamp[a] == k {
                    continue;
                }
                stamp[a] = k;
                match role[a] {
                    Role::Root => reads[k].push(a),
                    Role::Inline | Role::InlineWitness => stack.extend(p.ops[a].args().iter().map(|x| x.0 as usize)),
                    Role::Const => {}
                }
            }
            reads[k].sort();
        }
        let deps: Vec<Vec<usize>> = reads.iter().map(|rs| rs.iter().map(|a| index[*a]).collect()).collect();
        let bits: Vec<u64> = roots.iter().map(|r| p.tys[*r].as_ref().map_or(0, bits_of)).collect();
        let graph = crate::simplicity::sched::Graph::new(deps, bits);
        let sched = crate::simplicity::sched::schedule(&graph);
        let live_bits = crate::simplicity::sched::live_bits(&graph, &sched);
        let order: Vec<usize> = sched.iter().map(|k| roots[*k]).collect();
        let mut pos = vec![0usize; n];
        for (k, r) in order.iter().enumerate() {
            pos[*r] = k;
        }
        (roots, reads, live_bits, pos, order)
    }

    /// The first and last step (position in the order) that runs each value: a root runs in
    /// its own step and is read in its readers'; an inlined value runs where its readers run.
    fn owner_span(p: &Prog, readers: &[Vec<usize>], role: &[Role], pos: &[usize]) -> (Vec<usize>, Vec<usize>) {
        let n = p.ops.len();
        let (mut lo, mut hi) = (vec![usize::MAX; n], vec![0usize; n]);
        for i in (0..n).rev() {
            if role[i] == Role::Root {
                lo[i] = pos[i];
                hi[i] = pos[i];
            }
            for &r in &readers[i] {
                let (rl, rh) = if role[r] == Role::Root { (pos[r], pos[r]) } else { (lo[r], hi[r]) };
                if rl != usize::MAX {
                    lo[i] = lo[i].min(rl);
                    hi[i] = hi[i].max(rh);
                }
            }
            if lo[i] == usize::MAX {
                lo[i] = 0;
            }
        }
        (lo, hi)
    }

    /// The number of steps (roots).
    fn steps(&self) -> usize {
        self.order.len()
    }

    /// A constant, read from any environment: the constant itself (`1 -> T`) is one shared
    /// node, the `comp unit` that reads it is per use.
    fn constant(&mut self, t: &Ty, bytes: &[u8]) -> Term {
        let k = self.consts.entry((t.clone(), bytes.to_vec())).or_insert_with(|| const_term(t, bytes)).clone();
        Term::comp(&Term::unit(), &k)
    }

    /// The expression for value `v` given the environment `env` (stored values, in order).
    fn read(&mut self, v: Val) -> Term {
        let i = v.0 as usize;
        match (&self.p.ops[i], self.role[i]) {
            (Op::Const(t, b), _) => {
                let (t, b) = (t.clone(), b.clone());
                self.constant(&t, &b)
            }
            (Op::Witness(name, _), Role::InlineWitness) => self.witness(name),
            (_, Role::Inline) => {
                if let Some(t) = self.cache.get(&i) {
                    return t.clone();
                }
                let t = self.expr(i);
                self.cache.insert(i, t.clone());
                t
            }
            _ => {
                let slot = self.slot[i];
                assert!(slot != usize::MAX && self.occupant[slot] == Some(i), "a value read after it was dropped");
                #[cfg(test)]
                PATH_STATS.with(|c| {
                    let mut c = c.borrow_mut();
                    c.0 += 1;
                    c.1 += self.height;
                });
                Self::path(slot, self.height, 0, &Term::iden())
            }
        }
    }

    /// The path from the root of the environment tree (height `h`) to the node at `prefix`
    /// (its first `levels` bits of the slot number, most significant first), then `inner`.
    fn path(slot: usize, h: usize, levels_from_leaf: usize, inner: &Term) -> Term {
        // descend from the leaf's parent level upwards: innermost selector is the deepest bit
        let mut t = inner.clone();
        for bit in levels_from_leaf..h {
            t = if (slot >> bit) & 1 == 0 { Term::take(&t) } else { Term::drop_(&t) };
        }
        t
    }

    fn witness(&mut self, name: &Arc<str>) -> Term {
        self.witnesses.entry(name.clone()).or_insert_with(|| Term::witness(name)).clone()
    }

    /// The expression computing op `i`'s value from `env`.
    fn expr(&mut self, i: usize) -> Term {
        let op = self.p.ops[i].clone();
        match op {
            Op::Const(..) => unreachable!("constants are inline"),
            Op::Witness(name, _) => self.witness(&name),
            Op::Jet(name, args, _) => {
                if args.is_empty() {
                    return Term::comp(&Term::unit(), &Term::jet(name));
                }
                let tuple = self.tuple(&args);
                Term::comp(&tuple, &Term::jet(name))
            }
            Op::Unwrap(v, _) => {
                let x = self.read(v);
                Term::comp(&Term::pair(&x, &Term::unit()), &Term::assertr(&Term::take(&Term::iden())))
            }
            Op::Pair(a, b, _) => {
                let (x, y) = (self.read(a), self.read(b));
                Term::pair(&x, &y)
            }
            Op::Fst(v, _) => Term::comp(&self.read(v), &Term::take(&Term::iden())),
            Op::Snd(v, _) => Term::comp(&self.read(v), &Term::drop_(&Term::iden())),
            Op::Select(c, a, b, _) => {
                let (bit, x, y) = (self.read(c), self.read(a), self.read(b));
                Term::comp(&Term::pair(&bit, &Term::iden()), &Term::case(&Term::drop_(&y), &Term::drop_(&x)))
            }
            Op::Assert(_) => unreachable!("assertions are steps of their own"),
        }
    }

    /// Arguments paired right-nested.
    fn tuple(&mut self, args: &[Val]) -> Term {
        let first = self.read(args[0]);
        if args.len() == 1 {
            first
        } else {
            let rest = self.tuple(&args[1..]);
            Term::pair(&first, &rest)
        }
    }

    fn run(mut self) -> Term {
        // The environment is a binary tree of `2^height` slots (an empty subtree is `1`): a
        // value lives in a slot from its step to its last reader's step, a read is a path of
        // `height` selectors, and a step rebuilds only the paths to the slots it changes,
        // passing every other subtree on as one path.
        let mut steps = Vec::new();
        let order = self.order.clone();
        for (k, &i) in order.iter().enumerate() {
            self.cache.clear();
            // values read for the last time at this step leave after it
            let dying: Vec<usize> = self.occupant.iter().enumerate().filter_map(|(s, o)| o.filter(|v| self.last_use[*v] <= k).map(|_| s)).collect();
            let keep = !matches!(self.p.ops[i], Op::Assert(_)) && self.last_use[i] > k;
            let fresh = if matches!(self.p.ops[i], Op::Assert(_)) { None } else { Some(self.expr(i)) };
            let before = self.occupant.clone();
            for s in &dying {
                self.occupant[*s] = None;
            }
            let mut changes: BTreeMap<usize, Option<Term>> = dying.iter().map(|s| (*s, None)).collect();
            if keep {
                let s = self.occupant.iter().position(|o| o.is_none()).expect("a free slot");
                self.occupant[s] = Some(i);
                self.slot[i] = s;
                changes.insert(s, fresh.clone());
            }
            let rebuilt = self.rebuild(&before, &changes, self.height, 0);
            let step = match (&self.p.ops[i], keep) {
                (Op::Assert(b), _) => {
                    // read before the slots change
                    let occupant = std::mem::replace(&mut self.occupant, before.clone());
                    let bit = self.read(*b);
                    self.occupant = occupant;
                    let verify = Term::comp(&bit, &Term::jet("verify"));
                    Term::comp(&Term::pair(&verify, &rebuilt), &Term::drop_(&Term::iden()))
                }
                (_, true) => rebuilt,
                // a value nobody reads: computed and discarded
                (_, false) => Term::comp(&Term::pair(fresh.as_ref().unwrap(), &rebuilt), &Term::drop_(&Term::iden())),
            };
            steps.push(step);
        }
        // composition is associative: a balanced tree of `comp` keeps the program shallow
        steps.push(Term::unit());
        balanced(&steps)
    }

    /// The subtree of the environment at `prefix` (of `level` levels above the leaves) after the
    /// step's `changes` (slot -> new value or none), from the environment `before`.
    fn rebuild(&self, before: &[Option<usize>], changes: &BTreeMap<usize, Option<Term>>, level: usize, prefix: usize) -> Term {
        let lo = prefix << level;
        let hi = lo + (1 << level);
        let changed = changes.range(lo..hi).next().is_some();
        let occupied_after = (lo..hi).any(|s| match changes.get(&s) {
            Some(c) => c.is_some(),
            None => before[s].is_some(),
        });
        if !occupied_after {
            return Term::unit();
        }
        if !changed {
            // the same subtree as before: one path to it
            return Self::path(lo, self.height, level, &Term::iden());
        }
        if level == 0 {
            return changes[&lo].clone().expect("an occupied changed slot has a value");
        }
        let l = self.rebuild(before, changes, level - 1, prefix << 1);
        let r = self.rebuild(before, changes, level - 1, (prefix << 1) | 1);
        Term::pair(&l, &r)
    }
}

#[cfg(test)]
thread_local! {
    /// (reads of stored values, Σ of their depths): how much of the program is paths.
    pub(crate) static PATH_STATS: std::cell::RefCell<(usize, usize)> = std::cell::RefCell::new((0, 0));
}

/// The bits a value of type `t` takes in the environment.
pub(crate) fn bits_of(t: &Ty) -> u64 {
    match t {
        Ty::Bit => 1,
        Ty::Word(n) => *n as u64,
        Ty::Prod(a, b) => bits_of(a) + bits_of(b),
        Ty::Opt(t) => 1 + bits_of(t),
        Ty::Ctx => 838,
        Ty::CtxBuf => 518,
    }
}

/// 100 mWU per executed node (simplicity-lang 0.9 `Cost::OVERHEAD`).
const NODE: u64 = 100;
/// The environment's height assumed when deciding what to store.
const ASSUMED_HEIGHT: u64 = 6;
/// How a program is lowered; the compiler tries several and keeps the lightest program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Options {
    /// Passes deciding the roles: each after the first counts the arguments the previous one
    /// inlined in the cost of recomputing a value (fewer recomputations, more stored values:
    /// less cost, more bytes).
    pub(crate) role_passes: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options { role_passes: 1 }
    }
}

/// A lowered program and what it runs.
pub(crate) struct Lowered {
    pub(crate) term: Term,
    /// Jets by name, as run.
    pub(crate) jets: BTreeMap<&'static str, usize>,
    pub(crate) steps: usize,
    pub(crate) stored: usize,
    pub(crate) live_bits: u64,
}

/// A jet's fixed cost (simplicity-lang 0.9), mWU.
fn jet_cost(name: &str) -> u64 {
    use ::simplicity::jet::Jet as _;
    let j: ::simplicity::jet::Elements = name.parse().unwrap_or_else(|_| panic!("unknown jet {}", name));
    j.cost().to_string().parse().expect("a cost as an integer")
}

/// Computing op `i` once its arguments are at hand: the jet, its `comp` (which copies the
/// arguments) and the pairs that build them; or the selectors of a projection.
fn local_cost(p: &Prog, i: usize) -> u64 {
    let args = p.ops[i].args();
    let arg_bits: u64 = args.iter().map(|a| p.tys[a.0 as usize].as_ref().map_or(0, bits_of)).sum();
    let pairs = args.len().saturating_sub(1) as u64;
    match &p.ops[i] {
        Op::Jet(n, ..) => jet_cost(n) + 2 * NODE + arg_bits + pairs * NODE,
        Op::Pair(..) => NODE,
        Op::Fst(..) | Op::Snd(..) => 3 * NODE + arg_bits,
        Op::Unwrap(..) | Op::Select(..) => 5 * NODE + arg_bits,
        Op::Const(..) | Op::Witness(..) | Op::Assert(_) => 0,
    }
}

/// Reading a stored value: its path of selectors and the `iden` that copies it.
fn read_cost(bits: u64) -> u64 {
    NODE * (ASSUMED_HEIGHT + 1) + bits
}

/// Prefix sums with updates (roots decided so far, by position).
struct Fenwick(Vec<u64>);

impl Fenwick {
    fn new(n: usize) -> Self {
        Fenwick(vec![0; n + 1])
    }
    fn add(&mut self, i: usize) {
        let mut i = i + 1;
        while i < self.0.len() {
            self.0[i] += 1;
            i += i & i.wrapping_neg();
        }
    }
    /// Σ over positions `< i`.
    fn prefix(&self, i: usize) -> u64 {
        let (mut i, mut s) = (i, 0);
        while i > 0 {
            s += self.0[i];
            i -= i & i.wrapping_neg();
        }
        s
    }
}

/// `s_0 ; s_1 ; ... ; s_n` as a balanced tree of `comp`.
fn balanced(steps: &[Term]) -> Term {
    if steps.len() == 1 {
        return steps[0].clone();
    }
    let h = steps.len() / 2;
    Term::comp(&balanced(&steps[..h]), &balanced(&steps[h..]))
}

/// A constant of type `t` from its bytes (`1 -> T`).
fn const_term(t: &Ty, bytes: &[u8]) -> Term {
    match t {
        Ty::Bit => Term::bit(bytes[0] & 1 == 1),
        Ty::Word(_) => Term::word(bytes),
        Ty::Prod(a, b) => {
            let n = a.const_bytes();
            Term::pair(&const_term(a, &bytes[..n]), &const_term(b, &bytes[n..]))
        }
        Ty::Opt(_) | Ty::Ctx | Ty::CtxBuf => unreachable!(),
    }
}

/// Programs shared by the tests of several modules.
#[cfg(test)]
pub(crate) mod tests_support {
    use super::*;
    use crate::simplicity::run::word_value;
    use k256::elliptic_curve::ff::PrimeField as _;

    fn be(s: &k256::Scalar) -> Vec<u8> {
        s.to_repr().to_vec()
    }

    /// `inv(a b + c) = expected` with witnesses a, b, c.
    pub(crate) fn arithmetic_prog() -> Prog {
        let (a, b, c) = (k256::Scalar::from(11u64), k256::Scalar::from(13u64), k256::Scalar::from(17u64));
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
        p
    }

    /// Its witness, with `c` off by `c_off`.
    pub(crate) fn arithmetic_witness(c_off: u64) -> HashMap<Arc<str>, ::simplicity::Value> {
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("a"), word_value(&be(&k256::Scalar::from(11u64))));
        w.insert(Arc::<str>::from("b"), word_value(&be(&k256::Scalar::from(13u64))));
        w.insert(Arc::<str>::from("c"), word_value(&be(&k256::Scalar::from(17 + c_off))));
        w
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::run::{dummy_env, execute_term, word_value};
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
        execute_term(&p.to_term(), &w, &dummy_env(), false)
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
        let rep = execute_term(&p.to_term(), &w, &dummy_env(), false).unwrap();
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
            execute_term(&p.to_term(), &HashMap::new(), &dummy_env(), false)
        };
        assert!(run(gx).is_ok());
        assert!(run(vec![0u8; 32]).is_err());
    }

    fn hex_literal(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    /// A check nobody reads (decompress of x = 0, unwrapped) still runs once values read
    /// once are inlined.
    #[test]
    fn inlining_keeps_unread_effects() {
        let gx = hex_literal("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
        let run = |x: Vec<u8>| {
            let mut p = Prog::new();
            let bit = p.push(Op::Const(Ty::Bit, vec![0]));
            let xv = p.push(Op::Const(Ty::word(), x));
            let opt = p.push(Op::Jet("decompress", vec![bit, xv], Ty::opt(Ty::ge())));
            p.push(Op::Unwrap(opt, Ty::ge())); // read by nobody
            let one = p.push(Op::Const(Ty::word(), be(&sc(1))));
            let e = p.push(Op::Jet("eq_256", vec![one, one], Ty::Bit));
            p.push(Op::Assert(e));
            execute_term(&p.to_term(), &HashMap::new(), &dummy_env(), false)
        };
        assert!(run(gx).is_ok());
        assert!(run(vec![0u8; 32]).is_err());
    }

    /// A witness read once, deep in an inlined tree.
    #[test]
    fn inline_witness_read_once_deep() {
        let a = sc(9);
        let mut p = Prog::new();
        let wa = p.push(Op::Witness("a".into(), Ty::word()));
        let mut v = wa;
        for _ in 0..5 {
            v = p.push(Op::Jet("scalar_negate", vec![v], Ty::word()));
        }
        let k = p.push(Op::Const(Ty::word(), be(&(-a))));
        let e = p.push(Op::Jet("eq_256", vec![v, k], Ty::Bit));
        p.push(Op::Assert(e));
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("a"), word_value(&be(&a)));
        assert!(execute_term(&p.to_term(), &w, &dummy_env(), false).is_ok());
        assert_eq!(p.step_count(), 1, "the whole tree is one step");
    }

    /// A value read by three later operations is a step of its own (stored, computed once);
    /// read once, it is inlined into its reader.
    #[test]
    fn shared_value_is_stored() {
        let x = sc(5);
        let build = |readers: usize| {
            let mut p = Prog::new();
            let wx = p.push(Op::Witness("x".into(), Ty::word()));
            let inv = p.push(Op::Jet("scalar_invert", vec![wx], Ty::word()));
            let k = p.push(Op::Const(Ty::word(), be(&x.invert().unwrap())));
            for _ in 0..readers {
                let e = p.push(Op::Jet("eq_256", vec![inv, k], Ty::Bit));
                p.push(Op::Assert(e));
            }
            let mut w = HashMap::new();
            w.insert(Arc::<str>::from("x"), word_value(&be(&x)));
            assert!(execute_term(&p.to_term(), &w, &dummy_env(), false).is_ok());
            p.step_count()
        };
        // one reader: the assertion is the only step; three: the inversion and three assertions
        assert_eq!(build(1), 1);
        assert_eq!(build(3), 4);
    }

    /// Most operations of a transcript are read once: far fewer steps than operations.
    #[test]
    fn fewer_steps_than_ops() {
        use crate::simplicity::sha::{lower_log, CompileTranscript};
        use crate::TranscriptBackend;
        let mut t = CompileTranscript::new(b"steps");
        for i in 0..8u64 {
            t.append_u64(b"i", i);
            let mut d = [0u8; 64];
            t.challenge_bytes(b"c", &mut d);
        }
        let mut p = Prog::new();
        let ch = lower_log(&mut p, t.log(), 0, &mut |_, _, _| unreachable!());
        let mut acc = ch[0].scalar.unwrap();
        for c in &ch[1..] {
            acc = p.push(Op::Jet("scalar_add", vec![acc, c.scalar.unwrap()], Ty::word()));
        }
        let z = p.push(Op::Jet("scalar_is_zero", vec![acc], Ty::Bit));
        let nz = p.push(Op::Jet("complement_1", vec![z], Ty::Bit));
        p.push(Op::Assert(nz));
        assert!(p.step_count() * 2 < p.ops.len(), "{} steps for {} operations", p.step_count(), p.ops.len());
        assert!(execute_term(&p.to_term(), &HashMap::new(), &dummy_env(), false).is_ok());
    }


    /// A cheap value read by checks far apart is recomputed at each, not stored: the steps are
    /// the 43 checks and the two witnesses read several times.
    #[test]
    fn cheap_shared_value_is_recomputed() {
        let (x, y) = (sc(5), sc(9));
        let build = |bad: bool| {
            let mut p = Prog::new();
            let wx = p.push(Op::Witness("x".into(), Ty::word()));
            let wy = p.push(Op::Witness("y".into(), Ty::word()));
            let one = p.push(Op::Const(Ty::word(), be(&sc(1))));
            let s = p.push(Op::Jet("scalar_add", vec![wx, one], Ty::word()));
            let ks = p.push(Op::Const(Ty::word(), be(&(x + sc(1) + if bad { sc(1) } else { sc(0) }))));
            let ky = p.push(Op::Const(Ty::word(), be(&y)));
            for i in 0..43 {
                let e = if i % 20 == 0 { p.push(Op::Jet("eq_256", vec![s, ks], Ty::Bit)) } else { p.push(Op::Jet("eq_256", vec![wy, ky], Ty::Bit)) };
                p.push(Op::Assert(e));
            }
            p
        };
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("x"), word_value(&be(&x)));
        w.insert(Arc::<str>::from("y"), word_value(&be(&y)));
        let p = build(false);
        assert!(execute_term(&p.to_term(), &w, &dummy_env(), false).is_ok());
        assert_eq!(p.step_count(), 45);
        assert_eq!(p.stats()["scalar_add"], 3, "executed at each of its three readers");
        assert!(execute_term(&build(true).to_term(), &w, &dummy_env(), false).is_err());
    }

    /// A witness read through a value recomputed in several steps is stored (one path).
    #[test]
    fn witness_under_shared_inline_value_is_stored() {
        let x = sc(4);
        let mut p = Prog::new();
        let wx = p.push(Op::Witness("x".into(), Ty::word()));
        let n = p.push(Op::Jet("scalar_negate", vec![wx], Ty::word()));
        let k = p.push(Op::Const(Ty::word(), be(&(-x))));
        for _ in 0..3 {
            let e = p.push(Op::Jet("eq_256", vec![n, k], Ty::Bit));
            p.push(Op::Assert(e));
        }
        let mut w = HashMap::new();
        w.insert(Arc::<str>::from("x"), word_value(&be(&x)));
        assert!(execute_term(&p.to_term(), &w, &dummy_env(), false).is_ok());
        assert_eq!(p.stored_count(), 1, "the witness, not the negation");
    }

    /// A check inside a value recomputed in two steps runs (decompress of x = 0 fails).
    #[test]
    fn check_inside_shared_inline_value_runs() {
        let gx = hex_literal("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
        let run = |x: Vec<u8>| {
            let mut p = Prog::new();
            let bit = p.push(Op::Const(Ty::Bit, vec![0]));
            let xv = p.push(Op::Const(Ty::word(), x));
            let opt = p.push(Op::Jet("decompress", vec![bit, xv], Ty::opt(Ty::ge())));
            let ge = p.push(Op::Unwrap(opt, Ty::ge()));
            let gx2 = p.push(Op::Fst(ge, Ty::word()));
            for _ in 0..2 {
                let e = p.push(Op::Jet("eq_256", vec![gx2, xv], Ty::Bit));
                p.push(Op::Assert(e));
            }
            execute_term(&p.to_term(), &HashMap::new(), &dummy_env(), false)
        };
        assert!(run(gx).is_ok());
        assert!(run(vec![0u8; 32]).is_err());
    }
}

/// Random programs (suggested by the stage 2 review): every check must run after inlining,
/// scheduling and the slot tree.
#[cfg(test)]
pub(crate) mod random_programs {
    use super::*;
    use crate::simplicity::run::{dummy_env, execute_term, word_value};
    use k256::elliptic_curve::ff::PrimeField as _;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn be(s: &k256::Scalar) -> Vec<u8> {
        s.to_repr().to_vec()
    }

    /// Random scalar programs with checks at random nodes (and random selections between
    /// values); every check must run: perturbing any one of them must fail.
    pub(crate) fn build(seed: u64, n: usize, bad: Option<usize>) -> (Prog, HashMap<Arc<str>, ::simplicity::Value>, usize) {
        let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        let mut rnd = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let mut p = Prog::new();
        let mut w = HashMap::new();
        let mut vals: Vec<(Val, k256::Scalar)> = Vec::new();
        let mut checks = 0usize;
        for i in 0..4 {
            let s = k256::Scalar::from(rnd() % 1000 + 2);
            let name = format!("w{}", i);
            let v = p.push(Op::Witness(name.as_str().into(), Ty::word()));
            w.insert(Arc::<str>::from(name.as_str()), word_value(&be(&s)));
            vals.push((v, s));
        }
        for _ in 0..n {
            let r = rnd() % 10;
            // prefer recent values (single readers), sometimes old ones (shared, long-lived)
            let pick = |rnd: &mut dyn FnMut() -> u64, len: usize| if rnd() % 3 == 0 { (rnd() as usize) % len } else { len - 1 - (rnd() as usize) % len.min(3) };
            let a = vals[pick(&mut rnd, vals.len())];
            let b = vals[pick(&mut rnd, vals.len())];
            match r {
                0..=2 => { let v = p.push(Op::Jet("scalar_add", vec![a.0, b.0], Ty::word())); vals.push((v, a.1 + b.1)); }
                3..=4 => { let v = p.push(Op::Jet("scalar_multiply", vec![a.0, b.0], Ty::word())); vals.push((v, a.1 * b.1)); }
                5 => { let v = p.push(Op::Jet("scalar_negate", vec![a.0], Ty::word())); vals.push((v, -a.1)); }
                6 => {
                    // select between two values on a computed bit
                    let z = p.push(Op::Jet("scalar_is_zero", vec![a.0], Ty::Bit));
                    let v = p.push(Op::Select(z, a.0, b.0, Ty::word()));
                    vals.push((v, if bool::from(a.1.is_zero()) { a.1 } else { b.1 }));
                }
                7 => {
                    // a pair and its halves
                    let pr = p.push(Op::Pair(a.0, b.0, Ty::prod(Ty::word(), Ty::word())));
                    let f = p.push(Op::Fst(pr, Ty::word()));
                    let s = p.push(Op::Snd(pr, Ty::word()));
                    let v = p.push(Op::Jet("scalar_add", vec![f, s], Ty::word()));
                    vals.push((v, a.1 + b.1));
                }
                _ => {
                    let mut e = a.1;
                    if bad == Some(checks) { e += k256::Scalar::ONE; }
                    checks += 1;
                    let k = p.push(Op::Const(Ty::word(), be(&e)));
                    let q = p.push(Op::Jet("eq_256", vec![a.0, k], Ty::Bit));
                    p.push(Op::Assert(q));
                }
            }
        }
        // every witness read at least once
        let mut acc = vals[0];
        for j in 1..4 { let v = p.push(Op::Jet("scalar_add", vec![acc.0, vals[j].0], Ty::word())); acc = (v, acc.1 + vals[j].1); }
        let last = *vals.last().unwrap();
        let v = p.push(Op::Jet("scalar_add", vec![acc.0, last.0], Ty::word()));
        let (v, s) = (v, acc.1 + last.1);
        let mut e = s;
        if bad == Some(checks) { e += k256::Scalar::ONE; }
        checks += 1;
        let k = p.push(Op::Const(Ty::word(), be(&e)));
        let q = p.push(Op::Jet("eq_256", vec![v, k], Ty::Bit));
        p.push(Op::Assert(q));
        (p, w, checks)
    }

    #[test]
    fn random_programs_accept_and_every_check_runs() {
        let mut total = 0;
        for seed in 1..60u64 {
            for n in [5usize, 20, 60] {
                let (p, w, checks) = build(seed, n, None);
                let r = execute_term(&p.to_term(), &w, &dummy_env(), false);
                assert!(r.is_ok(), "seed {} n {}: {:?}", seed, n, r.err());
                for c in 0..checks {
                    let (p, w, _) = build(seed, n, Some(c));
                    assert!(execute_term(&p.to_term(), &w, &dummy_env(), false).is_err(), "seed {} n {} check {} skipped", seed, n, c);
                    total += 1;
                }
            }
        }
        println!("{} perturbed checks rejected", total);
    }

    /// Unwraps read by nobody, by a selection arm, by a selection condition's input.
    #[test]
    fn unwrap_in_select_arm_still_runs() {
        let gx = (0..64).step_by(2).map(|i| u8::from_str_radix(&"79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
        let run = |x: Vec<u8>, cond: u8| {
            let mut p = Prog::new();
            let bit = p.push(Op::Const(Ty::Bit, vec![0]));
            let xv = p.push(Op::Const(Ty::word(), x));
            let opt = p.push(Op::Jet("decompress", vec![bit, xv], Ty::opt(Ty::ge())));
            let ge = p.push(Op::Unwrap(opt, Ty::ge()));
            let gx2 = p.push(Op::Fst(ge, Ty::word()));
            let other = p.push(Op::Const(Ty::word(), vec![5u8; 32]));
            let c = p.push(Op::Const(Ty::Bit, vec![cond]));
            let s = p.push(Op::Select(c, gx2, other, Ty::word()));
            let e = p.push(Op::Jet("eq_256", vec![s, s], Ty::Bit));
            p.push(Op::Assert(e));
            execute_term(&p.to_term(), &HashMap::new(), &dummy_env(), false)
        };
        assert!(run(gx.clone(), 0).is_ok());
        assert!(run(gx, 1).is_ok());
        assert!(run(vec![0u8; 32], 1).is_err());
        assert!(run(vec![0u8; 32], 0).is_err(), "the unwrap in the untaken arm must still run");
    }
}

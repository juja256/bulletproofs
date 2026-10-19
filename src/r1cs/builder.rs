//! The circuit builder (spec §7): witnesses, products, lookups and reciprocal arguments on top
//! of [`ConstraintSystem`], recorded independently of the backend and lowered at `prove` /
//! `verify` to Bulletproofs (§7.5, logUp over randomized constraints) or to a BP++ reciprocal
//! form circuit (§7.6).

use std::collections::HashMap;

use curve25519_dalek::scalar::Scalar;
use clear_on_drop::clear::Clear;
use subtle::{Choice, ConstantTimeEq};

use super::{ConstraintSystem, LinearCombination, RandomizedConstraintSystem, Variable};
use crate::errors::R1CSError;

/// A column width, in bits.
pub type Width = u32;

/// Up to this many (row, lookup) pairs the multiplicities are counted directly (≈50 ns a
/// pair), beyond by an oblivious sort (both constant time; measured crossover: 2^16 rows and
/// 2^12 lookups take 0.8 s sorted, 13 s directly).
const DIRECT_COUNT_MAX: usize = 1 << 16;

/// Largest total width of a tuple: packed tuples stay below `2^252 < l`.
pub const MAX_TUPLE_BITS: u64 = 252;

/// A table created by [`CircuitBuilder::table`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableId(pub(super) usize);

/// Cost of a recorded circuit (spec §7.5, §7.6), computed as if it were finalized now.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    /// BP multipliers of the first phase (R1CS multipliers, witness pairs, products).
    pub bp_phase1: usize,
    /// BP multipliers of the second phase added by the builder (one per private term); the
    /// gadget's own randomized constraints come on top.
    pub bp_phase2: usize,
    /// Gates of the BP++ reciprocal form circuit, `N_p + N_m`.
    pub bppp_gates: usize,
    /// Length of the linear part of the BP++ commitments, `N_lin` (witnesses, multiplicities,
    /// input copies and copies beyond the `N_p + N_m` norm slots).
    pub bppp_lin: usize,
}

impl Cost {
    /// The `BulletproofGens` capacity the backend needs: BP the multipliers rounded up to a
    /// power of two (plus the gadget's own randomized multipliers, not counted here), BP++
    /// `max(N_p + N_m, N_lin + 6)`.
    pub fn gens_capacity(&self, backend: super::Backend) -> usize {
        match backend {
            super::Backend::Bp => (self.bp_phase1 + self.bp_phase2).next_power_of_two(),
            #[allow(unreachable_patterns)]
            _ => self.bppp_gates.max(self.bppp_lin + 6),
        }
    }
}

/// A reciprocal argument under construction (spec §7.2): terms `num / (X + pack(tuple))` whose
/// sum must vanish as a rational function of `X`. Recorded by
/// [`CircuitBuilder::finish_reciprocal`], which validates it.
#[derive(Clone, Debug)]
pub struct Reciprocal {
    pub(super) widths: Vec<Width>,
    pub(super) private: Vec<(LinearCombination, Vec<LinearCombination>)>,
    pub(super) public: Vec<(LinearCombination, Vec<u64>)>,
}

impl Reciprocal {
    /// The term `1 / (X + pack(tuple))`.
    pub fn add(&mut self, tuple: Vec<LinearCombination>) {
        self.add_weighted(Scalar::ONE.into(), tuple)
    }

    /// The term `-1 / (X + pack(tuple))`.
    pub fn sub(&mut self, tuple: Vec<LinearCombination>) {
        self.add_weighted((-Scalar::ONE).into(), tuple)
    }

    /// The term `num / (X + pack(tuple))`.
    pub fn add_weighted(&mut self, num: LinearCombination, tuple: Vec<LinearCombination>) {
        self.private.push((num, tuple));
    }

    /// The term `coeff / (X + pack(row))` for a public row.
    pub fn add_public(&mut self, coeff: LinearCombination, row: Vec<u64>) {
        self.public.push((coeff, row));
    }

    /// The width list.
    pub fn widths(&self) -> &[Width] {
        &self.widths
    }
}

/// Constraint systems that build circuits with lookups and reciprocal arguments (spec §7),
/// implemented by [`Prover`](super::Prover) and [`Verifier`](super::Verifier) for both
/// backends. All operations belong to the first phase; every variable they read must exist.
pub trait CircuitBuilder: ConstraintSystem {
    /// A free witness (BP: half a multiplier; BP++: a slot of `w_O`, no gate).
    fn witness(&mut self, v: Option<Scalar>) -> Result<Variable, R1CSError>;

    /// The constraint `l * r = out` (one multiplier, one BP++ gate).
    fn product(&mut self, l: LinearCombination, r: LinearCombination, out: LinearCombination) -> Result<(), R1CSError>;

    /// A public table with the given column widths; every entry of column `j` is below
    /// `2^widths[j]`, and the widths sum to at most 252 bits.
    fn table(&mut self, rows: Vec<Vec<u64>>, widths: &[Width]) -> Result<TableId, R1CSError>;

    /// Assert that `tuple` is a row of table `t`. For tables of two or more columns every
    /// component needs a proven bound (spec §7.3).
    fn lookup(&mut self, t: TableId, tuple: &[LinearCombination]) -> Result<(), R1CSError>;

    /// A witness that is an entry of the one-column table `t` (and bounded by its width).
    fn lookup_value(&mut self, t: TableId, v: Option<u64>) -> Result<Variable, R1CSError>;

    /// Start a reciprocal argument over tuples of the given widths.
    fn reciprocal(&mut self, widths: &[Width]) -> Result<Reciprocal, R1CSError> {
        check_widths(widths)?;
        Ok(Reciprocal { widths: widths.to_vec(), private: Vec::new(), public: Vec::new() })
    }

    /// Validate and record a reciprocal argument.
    fn finish_reciprocal(&mut self, r: Reciprocal) -> Result<(), R1CSError>;

    /// The cost of the circuit recorded so far.
    fn cost(&self) -> Cost;
}

pub(super) fn gadget_error(description: &str) -> R1CSError {
    R1CSError::GadgetError { description: description.into() }
}

pub(super) fn check_widths(widths: &[Width]) -> Result<(), R1CSError> {
    let total: u64 = widths.iter().map(|w| *w as u64).sum();
    if widths.is_empty() || widths.iter().any(|w| *w == 0) || total > MAX_TUPLE_BITS {
        return Err(gadget_error("invalid width list"));
    }
    Ok(())
}

fn check_row(row: &[u64], widths: &[Width]) -> Result<(), R1CSError> {
    if row.len() != widths.len() || row.iter().zip(widths).any(|(e, w)| *w < 64 && e >> *w != 0) {
        return Err(gadget_error("table row does not match the widths"));
    }
    Ok(())
}

/// The packing offsets `o_j` of a width list (spec §7.2).
pub(super) fn offsets(widths: &[Width]) -> Vec<u32> {
    let mut o = 0;
    widths
        .iter()
        .map(|w| {
            let x = o;
            o += w;
            x
        })
        .collect()
}

/// `2^e` for `e < 252`.
pub(super) fn pow2(e: u32) -> Scalar {
    let mut b = [0u8; 32];
    b[(e / 8) as usize] = 1 << (e % 8);
    Scalar::from_bytes_mod_order(b)
}

/// `pack(row) = sum_j 2^{o_j} row_j`.
pub(super) fn pack_row(row: &[u64], widths: &[Width]) -> Scalar {
    row.iter().zip(offsets(widths)).map(|(e, o)| pow2(o) * Scalar::from(*e)).sum()
}

/// A recorded table.
#[derive(Clone)]
pub(super) struct Table {
    pub(super) widths: Vec<Width>,
    pub(super) rows: Vec<Vec<u64>>,
    pub(super) queries: Vec<Vec<LinearCombination>>,
}

/// A recorded reciprocal argument: `(numerator, tuple)` private terms, `(coefficient, row)`
/// public terms.
pub(super) struct Argument {
    pub(super) widths: Vec<Width>,
    pub(super) private: Vec<(LinearCombination, Vec<LinearCombination>)>,
    pub(super) public: Vec<(LinearCombination, Vec<u64>)>,
}

/// The number of variables of each kind when an operation is called.
#[derive(Clone, Copy)]
pub(super) struct Counts {
    /// R1CS multipliers.
    pub(super) n: usize,
    /// Committed inputs.
    pub(super) k: usize,
}

/// The backend-independent record of the builder operations (spec §7.2).
#[derive(Default)]
pub(super) struct Builder {
    /// Set by the first builder operation (spec §7.2, builder mode).
    pub(super) active: bool,
    /// Witnesses so far (multiplicities included after finalization).
    pub(super) n_w: usize,
    pub(super) products: Vec<(LinearCombination, LinearCombination, LinearCombination)>,
    pub(super) tables: Vec<Table>,
    pub(super) args: Vec<Argument>,
    /// Recorded bounds `b_x` in bits (spec §7.3).
    bounds: HashMap<Variable, Width>,
    /// Test hook: count by the oblivious sort from this many (row, lookup) pairs on.
    #[cfg(test)]
    pub(super) direct_count_max: Option<usize>,
}

impl Builder {
    fn check_var(&self, x: Variable, c: Counts) -> Result<(), R1CSError> {
        let ok = match x {
            Variable::Committed(j) => j < c.k,
            Variable::MultiplierLeft(i) | Variable::MultiplierRight(i) | Variable::MultiplierOutput(i) => i < c.n,
            Variable::Witness(i) => i < self.n_w,
            Variable::One() => true,
        };
        if ok {
            Ok(())
        } else {
            Err(gadget_error("a builder operation uses a variable that does not exist"))
        }
    }

    pub(super) fn check_lc(&self, lc: &LinearCombination, c: Counts) -> Result<(), R1CSError> {
        lc.terms.iter().try_for_each(|(x, _)| self.check_var(*x, c))
    }

    /// The bound of an LC (spec §7.3): `c_0 + sum_x c_x (2^{b_x} - 1)`, or `None`.
    fn bound(&self, lc: &LinearCombination) -> Option<Big> {
        let mut merged: Vec<(Variable, Scalar)> = Vec::new();
        let mut c0 = Scalar::ZERO;
        for (x, c) in &lc.terms {
            match x {
                Variable::One() => c0 += c,
                _ => match merged.iter_mut().find(|(y, _)| y == x) {
                    Some((_, d)) => *d += c,
                    None => merged.push((*x, *c)),
                },
            }
        }
        let mut sum = Big::from_u64(small(&c0)?);
        for (x, c) in merged {
            if c == Scalar::ZERO {
                continue;
            }
            let b = *self.bounds.get(&x)?;
            sum = sum.add(&Big::pow2_minus_1(b).mul_u64(small(&c)?));
        }
        Some(sum)
    }

    /// Validate a tuple against a width list (spec §7.2, §7.3).
    fn check_tuple(&self, tuple: &[LinearCombination], widths: &[Width], c: Counts) -> Result<(), R1CSError> {
        if tuple.len() != widths.len() {
            return Err(gadget_error("tuple length does not match the widths"));
        }
        for lc in tuple {
            self.check_lc(lc, c)?;
        }
        if widths.len() >= 2 {
            for (lc, w) in tuple.iter().zip(widths) {
                match self.bound(lc) {
                    Some(b) if b.below_pow2(*w) => {}
                    _ => return Err(gadget_error("a tuple component has no bound below its width")),
                }
            }
        }
        Ok(())
    }

    pub(super) fn witness(&mut self) -> Variable {
        self.active = true;
        self.n_w += 1;
        Variable::Witness(self.n_w - 1)
    }

    pub(super) fn product(&mut self, l: LinearCombination, r: LinearCombination, out: LinearCombination, c: Counts) -> Result<(), R1CSError> {
        for lc in [&l, &r, &out] {
            self.check_lc(lc, c)?;
        }
        self.active = true;
        self.products.push((l, r, out));
        Ok(())
    }

    pub(super) fn table(&mut self, rows: Vec<Vec<u64>>, widths: &[Width]) -> Result<TableId, R1CSError> {
        check_widths(widths)?;
        if rows.is_empty() {
            return Err(gadget_error("empty table"));
        }
        for row in &rows {
            check_row(row, widths)?;
        }
        self.active = true;
        self.tables.push(Table { widths: widths.to_vec(), rows, queries: Vec::new() });
        Ok(TableId(self.tables.len() - 1))
    }

    fn get_table(&self, t: TableId) -> Result<&Table, R1CSError> {
        self.tables.get(t.0).ok_or_else(|| gadget_error("unknown table"))
    }

    pub(super) fn lookup(&mut self, t: TableId, tuple: &[LinearCombination], c: Counts) -> Result<(), R1CSError> {
        let widths = self.get_table(t)?.widths.clone();
        self.check_tuple(tuple, &widths, c)?;
        self.active = true;
        if widths.len() == 1 {
            if let [(x, coeff)] = tuple[0].terms[..] {
                if x != Variable::One() && coeff == Scalar::ONE {
                    let b = self.bounds.entry(x).or_insert(widths[0]);
                    *b = (*b).min(widths[0]);
                }
            }
        }
        self.tables[t.0].queries.push(tuple.to_vec());
        Ok(())
    }

    /// `lookup_value` needs a one-column table; checked before its witness is created.
    pub(super) fn check_value_table(&self, t: TableId) -> Result<(), R1CSError> {
        if self.get_table(t)?.widths.len() != 1 {
            return Err(gadget_error("lookup_value needs a one-column table"));
        }
        Ok(())
    }

    pub(super) fn finish_reciprocal(&mut self, r: Reciprocal, c: Counts) -> Result<(), R1CSError> {
        check_widths(&r.widths)?;
        for (num, tuple) in &r.private {
            self.check_lc(num, c)?;
            self.check_tuple(tuple, &r.widths, c)?;
        }
        for (coeff, row) in &r.public {
            self.check_lc(coeff, c)?;
            check_row(row, &r.widths)?;
        }
        self.active = true;
        if !r.private.is_empty() || !r.public.is_empty() {
            self.args.push(Argument { widths: r.widths, private: r.private, public: r.public });
        }
        Ok(())
    }

    /// The cost if finalized now, with `n` R1CS multipliers and `k` committed inputs.
    pub(super) fn cost(&self, n: usize, k: usize) -> Cost {
        let used = || self.tables.iter().filter(|t| !t.queries.is_empty());
        let n_w = self.n_w + used().map(|t| t.rows.len()).sum::<usize>();
        let n_p = self.args.iter().map(|a| a.private.len()).sum::<usize>() + used().map(|t| t.queries.len()).sum::<usize>();
        let n_prod = self.products.len();
        let n_r = if n == 0 && n_prod == 0 && n_p == 0 { 1 } else { n };
        let right = |lc: &LinearCombination| lc.terms.iter().any(|(x, _)| matches!(x, Variable::MultiplierRight(_)));
        let copies: usize = self
            .args
            .iter()
            .map(|a| a.private.iter().filter(|(num, _)| right(num)).count() + a.public.iter().filter(|(c, _)| right(c)).count())
            .sum();
        let gates = n_p + n_r + n_prod;
        Cost {
            bp_phase1: n + (n_w + 1) / 2 + n_prod,
            bp_phase2: n_p,
            bppp_gates: gates,
            bppp_lin: (n_r + k + n_w + copies).saturating_sub(gates),
        }
    }

    /// Finalization (spec §7.4): one multiplicity witness per row of each table with lookups,
    /// and the tables appended to the arguments. With `eval` (the prover) returns the
    /// multiplicities, or an error for a lookup equal to no row. Constant time in the witness:
    /// `|T|` comparisons per lookup, or an oblivious sort for large tables.
    pub(super) fn finalize(&mut self, eval: Option<&dyn Fn(&LinearCombination) -> Scalar>) -> Result<Vec<Scalar>, R1CSError> {
        let mut values = Vec::new();
        #[cfg(test)]
        let cheat = if eval.is_some() { cheat::get().multiplicities } else { None };
        #[cfg(not(test))]
        let cheat: Option<Vec<Scalar>> = None;
        let tables = core::mem::take(&mut self.tables);
        for table in tables.into_iter().filter(|t| !t.queries.is_empty()) {
            let first = self.n_w;
            self.n_w += table.rows.len();
            if let (Some(_), Some(m)) = (eval, &cheat) {
                values.extend(m[values.len()..values.len() + table.rows.len()].iter().copied());
            } else if let Some(eval) = eval {
                // Constant time in the witness: every lookup is compared with every row, or,
                // for large tables, an oblivious sort (same counts).
                #[cfg(test)]
                let direct_max = self.direct_count_max.unwrap_or(DIRECT_COUNT_MAX);
                #[cfg(not(test))]
                let direct_max = DIRECT_COUNT_MAX;
                let (m, all_found) = if table.rows.len().saturating_mul(table.queries.len()) <= direct_max {
                    let rows: Vec<Vec<Scalar>> = table.rows.iter().map(|r| r.iter().map(|e| Scalar::from(*e)).collect()).collect();
                    let mut m = vec![0u64; table.rows.len()];
                    let mut all_found = Choice::from(1u8);
                    for q in &table.queries {
                        let mut qv: Vec<Scalar> = q.iter().map(|lc| eval(lc)).collect();
                        let mut found = Choice::from(0u8);
                        for (r, row) in rows.iter().enumerate() {
                            let eq = qv.iter().zip(row).fold(Choice::from(1u8), |acc, (x, y)| acc & x.ct_eq(y));
                            m[r] += (eq & !found).unwrap_u8() as u64;
                            found |= eq;
                        }
                        all_found &= found;
                        qv.iter_mut().for_each(|x| x.clear());
                    }
                    (m, all_found)
                } else {
                    let key = |xs: &mut dyn Iterator<Item = Scalar>| xs.flat_map(|x| x.to_bytes()).collect::<Vec<u8>>();
                    let rows: Vec<Vec<u8>> = table.rows.iter().map(|r| key(&mut r.iter().map(|e| Scalar::from(*e)))).collect();
                    let mut lookups: Vec<Vec<u8>> = table.queries.iter().map(|q| key(&mut q.iter().map(|lc| eval(lc)))).collect();
                    let out = super::oblivious::count(&rows, &lookups);
                    lookups.iter_mut().flatten().for_each(|b| *b = 0);
                    out
                };
                if !bool::from(all_found) {
                    return Err(gadget_error("lookup query is not a table row"));
                }
                values.extend(m.into_iter().map(Scalar::from));
            }
            let private = table.queries.into_iter().map(|q| (Scalar::ONE.into(), q)).collect();
            let public = (0..table.rows.len())
                .zip(table.rows)
                .map(|(r, row)| (LinearCombination::from(Variable::Witness(first + r)) * (-Scalar::ONE), row))
                .collect();
            self.args.push(Argument { widths: table.widths, private, public });
        }
        Ok(values)
    }
}

/// Test-only cheating provers: replace the honest multiplicities, the denominators or the
/// numerators of the BP lowering, so that tests can check that the verifier catches them.
#[cfg(test)]
pub(super) mod cheat {
    use core::cell::RefCell;
    use curve25519_dalek::scalar::Scalar;

    #[derive(Clone, Default)]
    pub(crate) struct Cheat {
        /// Multiplicities instead of the counts (all tables, in order); skips the row check.
        pub(crate) multiplicities: Option<Vec<Scalar>>,
        /// BP: every private term's denominator is that of this public row.
        pub(crate) denominator_row: Option<Vec<u64>>,
        /// BP: every private term's numerator value is this.
        pub(crate) numerator: Option<Scalar>,
    }

    thread_local! {
        pub(crate) static CHEAT: RefCell<Cheat> = RefCell::new(Cheat::default());
    }

    pub(crate) fn get() -> Cheat {
        CHEAT.with(|c| c.borrow().clone())
    }

    pub(crate) fn set(c: Cheat) {
        CHEAT.with(|x| *x.borrow_mut() = c);
    }
}

/// The BP lowering of one argument (spec §7.5, a port of bpvm's `LogUp`): challenges `alpha`
/// (for tuples of two or more components) and `c`; one multiplier `r * d = num` with
/// `d = c + sum_j alpha^j x_j` per private term; `sum r + sum coeff / d(row) = 0`.
pub(super) fn logup<CS: RandomizedConstraintSystem>(cs: &mut CS, arg: Argument) -> Result<(), R1CSError> {
    let m = arg.widths.len();
    let alpha = if m > 1 { cs.challenge_scalar(b"logup alpha") } else { Scalar::ONE };
    let c = cs.challenge_scalar(b"logup c");
    let pows: Vec<Scalar> = core::iter::successors(Some(Scalar::ONE), |p| Some(p * alpha)).take(m).collect();
    let zero = || gadget_error("a reciprocal argument has a zero denominator");
    let compress = |x: Vec<LinearCombination>| x.into_iter().zip(&pows).fold(LinearCombination::from(c), |acc, (lc, a)| acc + lc * *a);
    // The prover's denominators and numerators (the verifier evaluates to `None`).
    let mut den = Vec::with_capacity(arg.private.len());
    let mut num = Vec::with_capacity(arg.private.len());
    for (n, x) in &arg.private {
        let d = x.iter().zip(&pows).try_fold(c, |acc, (lc, a)| cs.eval(lc).map(|v| acc + v * a));
        den.push(d);
        num.push(cs.eval(n));
    }
    #[cfg(test)]
    {
        let ch = cheat::get();
        if let Some(row) = ch.denominator_row {
            let d = row.iter().zip(&pows).fold(c, |acc, (e, a)| acc + Scalar::from(*e) * a);
            den.iter_mut().filter(|x| x.is_some()).for_each(|x| *x = Some(d));
        }
        if let Some(v) = ch.numerator {
            num.iter_mut().filter(|x| x.is_some()).for_each(|x| *x = Some(v));
        }
    }
    let prover = den.iter().all(Option::is_some) && num.iter().all(Option::is_some) && !arg.private.is_empty();
    let mut inv: Option<Vec<Scalar>> = if prover {
        let mut d: Vec<Scalar> = den.iter().map(|x| x.unwrap()).collect();
        if d.iter().any(|x| *x == Scalar::ZERO) {
            return Err(zero());
        }
        Scalar::batch_invert(&mut d);
        Some(d)
    } else {
        None
    };
    let mut sum = LinearCombination::default();
    for (q, (n, x)) in arg.private.into_iter().enumerate() {
        let assignment = inv.as_ref().map(|inv| (num[q].unwrap() * inv[q], den[q].unwrap()));
        let (r, d, o) = cs.allocate_multiplier(assignment)?;
        cs.constrain(d - compress(x));
        cs.constrain(o - n);
        sum = sum + r;
    }
    let mut pub_den: Vec<Scalar> =
        arg.public.iter().map(|(_, row)| row.iter().zip(&pows).fold(c, |acc, (e, a)| acc + Scalar::from(*e) * a)).collect();
    if pub_den.iter().any(|x| *x == Scalar::ZERO) {
        return Err(zero());
    }
    if !pub_den.is_empty() {
        Scalar::batch_invert(&mut pub_den);
    }
    for ((coeff, _), w) in arg.public.into_iter().zip(pub_den) {
        sum = sum + coeff * w;
    }
    cs.constrain(sum);
    for x in den.iter_mut().chain(num.iter_mut()).flatten() {
        x.clear();
    }
    for x in inv.iter_mut().flatten() {
        x.clear();
    }
    Ok(())
}

/// A scalar as an integer below `2^64`, if it is one.
fn small(c: &Scalar) -> Option<u64> {
    let b = c.as_bytes();
    if b[8..].iter().all(|x| *x == 0) {
        let mut lo = [0u8; 8];
        lo.copy_from_slice(&b[..8]);
        Some(u64::from_le_bytes(lo))
    } else {
        None
    }
}

/// Unsigned integers of 512 bits (enough for bounds: terms below `2^316`), saturating.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Big([u64; 8]);

impl Big {
    fn from_u64(x: u64) -> Self {
        let mut l = [0; 8];
        l[0] = x;
        Big(l)
    }

    /// `2^b - 1`, `b <= 252`.
    fn pow2_minus_1(b: Width) -> Self {
        let mut l = [0u64; 8];
        for (i, x) in l.iter_mut().enumerate() {
            let lo = 64 * i as u32;
            if b >= lo + 64 {
                *x = u64::MAX;
            } else if b > lo {
                *x = (1u64 << (b - lo)) - 1;
            }
        }
        Big(l)
    }

    fn saturated() -> Self {
        Big([u64::MAX; 8])
    }

    fn add(&self, o: &Big) -> Big {
        let mut l = [0u64; 8];
        let mut carry = 0u128;
        for i in 0..8 {
            let s = self.0[i] as u128 + o.0[i] as u128 + carry;
            l[i] = s as u64;
            carry = s >> 64;
        }
        if carry != 0 {
            Big::saturated()
        } else {
            Big(l)
        }
    }

    fn mul_u64(&self, c: u64) -> Big {
        let mut l = [0u64; 8];
        let mut carry = 0u128;
        for i in 0..8 {
            let p = self.0[i] as u128 * c as u128 + carry;
            l[i] = p as u64;
            carry = p >> 64;
        }
        if carry != 0 {
            Big::saturated()
        } else {
            Big(l)
        }
    }

    /// `self < 2^w`.
    fn below_pow2(&self, w: Width) -> bool {
        self.0.iter().enumerate().all(|(i, x)| {
            let lo = 64 * i as u32;
            if w >= lo + 64 {
                true
            } else if w > lo {
                x >> (w - lo) == 0
            } else {
                *x == 0
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const C: Counts = Counts { n: 2, k: 1 };

    fn lc(terms: &[(Variable, u64)]) -> LinearCombination {
        terms.iter().map(|(x, c)| (*x, Scalar::from(*c))).collect()
    }

    /// A builder with witnesses `W0..W3`, `W0`, `W1` bounded by 4 bits through a one-column table.
    fn bounded() -> (Builder, TableId) {
        let mut b = Builder::default();
        for _ in 0..4 {
            b.witness();
        }
        let t = b.table((0..16).map(|x| vec![x]).collect(), &[4]).unwrap();
        b.lookup(t, &[Variable::Witness(0).into()], C).unwrap();
        b.lookup(t, &[Variable::Witness(1).into()], C).unwrap();
        (b, t)
    }

    #[test]
    fn widths_and_tables_are_validated() {
        let mut b = Builder::default();
        assert!(b.table(vec![vec![1]], &[]).is_err());
        assert!(b.table(vec![vec![1]], &[0]).is_err());
        assert!(b.table(vec![vec![1, 1]], &[126, 127]).is_err(), "253 bits");
        assert!(b.table(vec![vec![1, 1]], &[126, 126]).is_ok(), "252 bits");
        assert!(b.table(Vec::<Vec<u64>>::new(), &[8]).is_err(), "empty");
        assert!(b.table(vec![vec![256]], &[8]).is_err(), "entry >= 2^w");
        assert!(b.table(vec![vec![255]], &[8]).is_ok());
        assert!(b.table(vec![vec![u64::MAX]], &[64]).is_ok());
        assert!(b.table(vec![vec![1]], &[4, 4]).is_err(), "row length");
        assert_eq!(b.tables.len(), 3);
    }

    #[test]
    fn bound_rule() {
        let (mut b, _) = bounded();
        let (w0, w1, w2) = (Variable::Witness(0), Variable::Witness(1), Variable::Witness(2));
        let t2 = b.table(vec![vec![0, 0]], &[8, 8]).unwrap();
        // w0 + 16 w1 <= 255: fits 8 bits; plus 1 does not
        assert!(b.lookup(t2, &[lc(&[(w0, 1), (w1, 16)]), w0.into()], C).is_ok());
        assert!(b.lookup(t2, &[lc(&[(w0, 1), (w1, 16), (Variable::One(), 1)]), w0.into()], C).is_err());
        // a bound of exactly 2^w - 1 is accepted, 2^w is not (w0 has 4 bits: 15 * 17 = 255)
        assert!(b.lookup(t2, &[lc(&[(w0, 17)]), w0.into()], C).is_ok());
        assert!(b.lookup(t2, &[lc(&[(w0, 17), (Variable::One(), 1)]), w0.into()], C).is_err());
        // unbounded, negative, too large a coefficient; merged terms; zero coefficients
        assert!(b.lookup(t2, &[w2.into(), w0.into()], C).is_err(), "unbounded");
        assert!(b.lookup(t2, &[w0 * (-Scalar::ONE), w0.into()], C).is_err(), "negative");
        assert!(b.lookup(t2, &[w0 * Scalar::from(1u128 << 64), w0.into()], C).is_err(), "2^64");
        assert!(b.lookup(t2, &[w0 + w0 * Scalar::from(16u64), w0.into()], C).is_ok(), "17 w0 merged");
        assert!(b.lookup(t2, &[w0 - w0 + w2 * Scalar::ZERO, w0.into()], C).is_ok(), "zero coefficients");
        assert!(b.lookup(t2, &[(w0 + w0) - w0, w0.into()], C).is_ok(), "merged 1 + 1 - 1");
    }

    #[test]
    fn bounds_come_from_single_term_lookups_only() {
        let (mut b, t) = bounded();
        let (w2, w3) = (Variable::Witness(2), Variable::Witness(3));
        let t2 = b.table(vec![vec![0, 0]], &[8, 8]).unwrap();
        b.lookup(t, &[w2 * Scalar::from(2u64)], C).unwrap(); // coefficient 2: no bound
        b.lookup(t, &[w3 + Scalar::ZERO], C).unwrap(); // two terms: no bound
        assert!(b.lookup(t2, &[w2.into(), w2.into()], C).is_err());
        assert!(b.lookup(t2, &[w3.into(), w3.into()], C).is_err());
        b.lookup(t, &[w3.into()], C).unwrap();
        assert!(b.lookup(t2, &[w3.into(), w3.into()], C).is_ok());
        // the tighter of two bounds wins
        let wide = b.table(vec![vec![0]], &[200]).unwrap();
        b.lookup(wide, &[w3.into()], C).unwrap();
        assert_eq!(b.bounds[&w3], 4);
        // a one-component tuple needs no bound
        let field = b.table(vec![vec![0]], &[252]).unwrap();
        assert!(b.lookup(field, &[w2 * (-Scalar::ONE)], C).is_ok());
    }

    #[test]
    fn variables_must_exist() {
        let (mut b, t) = bounded();
        assert!(b.lookup(t, &[Variable::Witness(4).into()], C).is_err());
        assert!(b.lookup(t, &[Variable::MultiplierRight(2).into()], C).is_err());
        assert!(b.lookup(t, &[Variable::MultiplierOutput(1).into()], C).is_ok());
        assert!(b.lookup(t, &[Variable::Committed(1).into()], C).is_err());
        assert!(b.product(Variable::Witness(9).into(), Scalar::ONE.into(), Scalar::ONE.into(), C).is_err());
        assert!(b.lookup(TableId(7), &[Scalar::ONE.into()], C).is_err());
        assert!(b.lookup(t, &[Scalar::ONE.into(), Scalar::ONE.into()], C).is_err(), "tuple length");
        let before = b.tables[t.0].queries.len();
        assert!(b.lookup(t, &[Variable::Witness(4).into()], C).is_err());
        assert_eq!(b.tables[t.0].queries.len(), before, "a failed operation records nothing");
    }

    #[test]
    fn reciprocals_are_validated() {
        let (mut b, _) = bounded();
        let (w0, w1, w2) = (Variable::Witness(0), Variable::Witness(1), Variable::Witness(2));
        let new = |w: &[Width]| Reciprocal { widths: w.to_vec(), private: vec![], public: vec![] };
        let mut r = new(&[4, 4]);
        r.add(vec![w0.into(), w1.into()]);
        r.add_public(w2.into(), vec![15, 15]);
        assert!(b.finish_reciprocal(r.clone(), C).is_ok());
        let mut x = r.clone();
        x.add_public(Scalar::ONE.into(), vec![16, 0]);
        assert!(b.finish_reciprocal(x, C).is_err(), "row entry >= 2^w");
        let mut x = r.clone();
        x.add_public(Scalar::ONE.into(), vec![1]);
        assert!(b.finish_reciprocal(x, C).is_err(), "row length");
        let mut x = r.clone();
        x.sub(vec![w2.into(), w0.into()]);
        assert!(b.finish_reciprocal(x, C).is_err(), "unbounded component");
        let mut x = r.clone();
        x.add_weighted(Variable::Witness(8).into(), vec![w0.into(), w1.into()]);
        assert!(b.finish_reciprocal(x, C).is_err(), "unknown numerator variable");
        // one component: any LC
        let mut x = new(&[252]);
        x.add_weighted(w2.into(), vec![w2 * Scalar::from(7u64) + Scalar::ONE]);
        assert!(b.finish_reciprocal(x, C).is_ok());
        assert_eq!(b.args.len(), 2);
        assert!(b.finish_reciprocal(new(&[8]), C).is_ok());
        assert_eq!(b.args.len(), 2, "an empty argument is dropped");
    }

    #[test]
    fn finalize_counts_first_equal_row() {
        let mut b = Builder::default();
        let w: Vec<Variable> = (0..3).map(|_| b.witness()).collect();
        let t = b.table(vec![vec![1], vec![2], vec![1]], &[2]).unwrap();
        let _unused = b.table(vec![vec![0]], &[1]).unwrap();
        for x in &w {
            b.lookup(t, &[(*x).into()], C).unwrap();
        }
        let vals = [Scalar::from(1u64), Scalar::from(2u64), Scalar::from(1u64)];
        let eval = |lc: &LinearCombination| {
            lc.terms.iter().map(|(x, c)| c * if let Variable::Witness(i) = x { vals[*i] } else { Scalar::ONE }).sum()
        };
        let cost = b.cost(0, 0);
        let m = b.finalize(Some(&eval)).unwrap();
        assert_eq!(m, vec![Scalar::from(2u64), Scalar::ONE, Scalar::ZERO]);
        assert_eq!(b.n_w, 6, "multiplicities of used tables only");
        assert_eq!(b.args.len(), 1);
        assert_eq!(b.args[0].public[0].0, LinearCombination::from(Variable::Witness(3)) * (-Scalar::ONE));
        assert_eq!(cost, Cost { bp_phase1: 3, bp_phase2: 3, bppp_gates: 3, bppp_lin: 3 });
        // a query equal to no row
        let mut b = Builder::default();
        let x = b.witness();
        let t = b.table(vec![vec![1]], &[2]).unwrap();
        b.lookup(t, &[x.into()], C).unwrap();
        let zero = |_: &LinearCombination| Scalar::ZERO;
        assert!(b.finalize(Some(&zero)).is_err());
    }

    /// The oblivious sort gives the multiplicities of the direct count (duplicate rows, a
    /// multi-column table, a lookup equal to no row).
    #[test]
    fn oblivious_counting_matches_direct() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        for trial in 0..40 {
            let mut b = Builder::default();
            let n_w = rng.gen_range(1..30);
            let vals: Vec<(u64, u64)> = (0..n_w).map(|_| (rng.gen_range(0..6), rng.gen_range(0..3))).collect();
            let w: Vec<Variable> = (0..2 * n_w).map(|_| b.witness()).collect();
            let rows: Vec<Vec<u64>> = (0..rng.gen_range(1..20)).map(|_| vec![rng.gen_range(0..6), rng.gen_range(0..3)]).collect();
            let range = b.table((0..8).map(|x| vec![x]).collect(), &[3]).unwrap();
            let t = b.table(rows, &[3, 3]).unwrap();
            for x in &w {
                b.lookup(range, &[(*x).into()], C).unwrap();
            }
            for i in 0..n_w {
                b.lookup(t, &[w[2 * i].into(), w[2 * i + 1].into()], C).unwrap();
            }
            let eval = |lc: &LinearCombination| {
                lc.terms
                    .iter()
                    .map(|(x, c)| match x {
                        Variable::Witness(i) => c * Scalar::from(if i % 2 == 0 { vals[i / 2].0 } else { vals[i / 2].1 }),
                        _ => *c,
                    })
                    .sum()
            };
            let mut b2 = Builder { direct_count_max: Some(0), tables: b.tables.clone(), n_w: b.n_w, ..Builder::default() };
            let direct = b.finalize(Some(&eval));
            let sorted = b2.finalize(Some(&eval));
            assert_eq!(direct.is_ok(), sorted.is_ok(), "trial {}", trial);
            if let (Ok(d), Ok(s)) = (direct, sorted) {
                assert_eq!(d, s, "trial {}", trial);
            }
        }
    }

    #[test]
    fn big_integers() {
        assert!(Big::pow2_minus_1(252).below_pow2(252));
        assert!(!Big::pow2_minus_1(252).add(&Big::from_u64(1)).below_pow2(252));
        assert!(Big::pow2_minus_1(64).below_pow2(64));
        assert!(!Big::from_u64(1 << 63).mul_u64(2).below_pow2(64));
        assert!(Big::pow2_minus_1(252).mul_u64(u64::MAX).below_pow2(316));
        assert!(!Big::saturated().below_pow2(252));
        assert_eq!(pow2(0), Scalar::ONE);
        assert_eq!(pow2(251), (0..251).fold(Scalar::ONE, |a, _| a + a));
        assert_eq!(pack_row(&[3, 1], &[2, 5]), Scalar::from(7u64));
        assert_eq!(offsets(&[2, 5, 1]), vec![0, 2, 7]);
    }
}

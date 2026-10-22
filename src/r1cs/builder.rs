//! The circuit builder (spec §7): the record of witnesses, products, lookups and reciprocal
//! arguments of a [`ConstraintSystem`], independent of the backend and lowered at `prove` /
//! `verify` to Bulletproofs (§7.5, logUp over randomized constraints) or to a BP++ reciprocal
//! form circuit (§7.6).

use subtle::Choice;

use super::{ConstraintSystem, LinearCombination, RandomizedConstraintSystem, Variable};
use crate::curve::Field;
use crate::errors::R1CSError;

/// Up to this many (row, lookup) pairs the multiplicities are counted directly (≈50 ns a
/// pair), beyond by an oblivious sort (both constant time; measured crossover: 2^16 rows and
/// 2^12 lookups take 0.8 s sorted, 13 s directly).
const DIRECT_COUNT_MAX: usize = 1 << 16;

/// A table created by [`ConstraintSystem::table`].
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
    pub bppp_linear: usize,
}

impl Cost {
    /// BP: multipliers of both phases; BP++: gates `N_p + N_m`.
    pub fn gates(&self, backend: super::Backend) -> usize {
        match backend {
            super::Backend::Bp => self.bp_phase1 + self.bp_phase2,
            super::Backend::Bppp => self.bppp_gates,
        }
    }

    /// BP++: the linear slots `N_lin`; BP: 0.
    pub fn linear(&self, backend: super::Backend) -> usize {
        match backend {
            super::Backend::Bp => 0,
            super::Backend::Bppp => self.bppp_linear,
        }
    }

    /// The `BulletproofGens` capacity the backend needs: BP the multipliers rounded up to a
    /// power of two (plus the gadget's own randomized multipliers, not counted here), BP++
    /// `max(N_p + N_m, N_lin + 6)` ([`BpppGens::capacity`](crate::bppp::BpppGens::capacity)).
    pub fn gens_capacity(&self, backend: super::Backend) -> usize {
        match backend {
            super::Backend::Bp => (self.bp_phase1 + self.bp_phase2).next_power_of_two(),
            super::Backend::Bppp => crate::bppp::gens_capacity(self.bppp_linear, self.bppp_gates),
        }
    }
}

/// A reciprocal argument (spec §7.2): a sum of terms `num / (X + tuple)` over tuples of `m`
/// components that must vanish as a rational function in `X`, i.e. the terms cancel per
/// tuple (a multiset equality, a lookup, a permutation). Created by
/// [`ConstraintSystem::reciprocal`] and recorded at once; each term is validated when it is
/// added. An argument without terms adds nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reciprocal(pub(super) usize);

impl Reciprocal {
    /// Add the term `1 / (X + tuple)`.
    pub fn add<F: Field, CS: ConstraintSystem<F> + ?Sized>(self, cs: &mut CS, tuple: &[LinearCombination<F>]) -> Result<(), R1CSError> {
        cs.reciprocal_term(self, F::ONE.into(), tuple)
    }

    /// Add the term `-1 / (X + tuple)`.
    pub fn sub<F: Field, CS: ConstraintSystem<F> + ?Sized>(self, cs: &mut CS, tuple: &[LinearCombination<F>]) -> Result<(), R1CSError> {
        cs.reciprocal_term(self, (-F::ONE).into(), tuple)
    }

    /// Add the term `num / (X + tuple)`.
    pub fn add_weighted<F: Field, CS: ConstraintSystem<F> + ?Sized>(self, cs: &mut CS, num: LinearCombination<F>, tuple: &[LinearCombination<F>]) -> Result<(), R1CSError> {
        cs.reciprocal_term(self, num, tuple)
    }

    /// Add the term `coeff / (X + row)` for a public row.
    pub fn add_public<F: Field, CS: ConstraintSystem<F> + ?Sized>(self, cs: &mut CS, coeff: LinearCombination<F>, row: &[u64]) -> Result<(), R1CSError> {
        cs.reciprocal_public(self, coeff, row)
    }
}

pub(super) fn gadget_error(description: &str) -> R1CSError {
    R1CSError::GadgetError { description: description.into() }
}

/// A recorded table.
#[derive(Clone)]
pub(super) struct Table<F: Field> {
    /// Columns.
    pub(super) m: usize,
    pub(super) rows: Vec<Vec<u64>>,
    pub(super) queries: Vec<Vec<LinearCombination<F>>>,
}

/// A recorded reciprocal argument: `(numerator, tuple)` private terms, `(coefficient, row)`
/// public terms.
pub(super) struct Argument<F: Field> {
    /// Components of every tuple and row.
    pub(super) m: usize,
    pub(super) private: Vec<(LinearCombination<F>, Vec<LinearCombination<F>>)>,
    pub(super) public: Vec<(LinearCombination<F>, Vec<u64>)>,
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
pub(super) struct Builder<F: Field> {
    /// Witnesses so far (multiplicities included after finalization).
    pub(super) n_w: usize,
    pub(super) products: Vec<(LinearCombination<F>, LinearCombination<F>, LinearCombination<F>)>,
    pub(super) tables: Vec<Table<F>>,
    pub(super) args: Vec<Argument<F>>,
    /// Test hook: count by the oblivious sort from this many (row, lookup) pairs on.
    #[cfg(test)]
    pub(super) direct_count_max: Option<usize>,
}

impl<F: Field> Default for Builder<F> {
    fn default() -> Self {
        Builder {
            n_w: 0,
            products: Vec::new(),
            tables: Vec::new(),
            args: Vec::new(),
            #[cfg(test)]
            direct_count_max: None,
        }
    }
}

impl<F: Field> Builder<F> {
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

    pub(super) fn check_lc(&self, lc: &LinearCombination<F>, c: Counts) -> Result<(), R1CSError> {
        lc.terms.iter().try_for_each(|(x, _)| self.check_var(*x, c))
    }

    /// Validate a tuple of `m` components (spec §7.2).
    fn check_tuple(&self, tuple: &[LinearCombination<F>], m: usize, c: Counts) -> Result<(), R1CSError> {
        if tuple.len() != m {
            return Err(gadget_error("tuple length does not match the columns"));
        }
        tuple.iter().try_for_each(|lc| self.check_lc(lc, c))
    }

    pub(super) fn witness(&mut self) -> Variable {
        self.n_w += 1;
        Variable::Witness(self.n_w - 1)
    }

    pub(super) fn constrain_product(&mut self, l: LinearCombination<F>, r: LinearCombination<F>, out: LinearCombination<F>, c: Counts) -> Result<(), R1CSError> {
        for lc in [&l, &r, &out] {
            self.check_lc(lc, c)?;
        }
        self.products.push((l, r, out));
        Ok(())
    }

    pub(super) fn table(&mut self, rows: Vec<Vec<u64>>) -> Result<TableId, R1CSError> {
        let m = match rows.first() {
            None => return Err(gadget_error("empty table")),
            Some(r) if r.is_empty() => return Err(gadget_error("a table needs at least one column")),
            Some(r) => r.len(),
        };
        if rows.iter().any(|r| r.len() != m) {
            return Err(gadget_error("table rows of different lengths"));
        }
        self.tables.push(Table { m, rows, queries: Vec::new() });
        Ok(TableId(self.tables.len() - 1))
    }

    fn get_table(&self, t: TableId) -> Result<&Table<F>, R1CSError> {
        self.tables.get(t.0).ok_or_else(|| gadget_error("unknown table"))
    }

    pub(super) fn lookup(&mut self, t: TableId, tuple: &[LinearCombination<F>], c: Counts) -> Result<(), R1CSError> {
        let m = self.get_table(t)?.m;
        self.check_tuple(tuple, m, c)?;
        self.tables[t.0].queries.push(tuple.to_vec());
        Ok(())
    }

    /// `lookup_value` needs a one-column table; checked before its witness is created.
    pub(super) fn check_value_table(&self, t: TableId) -> Result<(), R1CSError> {
        if self.get_table(t)?.m != 1 {
            return Err(gadget_error("lookup_value needs a one-column table"));
        }
        Ok(())
    }

    pub(super) fn reciprocal(&mut self, m: usize) -> Result<Reciprocal, R1CSError> {
        if m == 0 {
            return Err(gadget_error("a reciprocal argument needs at least one column"));
        }
        self.args.push(Argument { m, private: Vec::new(), public: Vec::new() });
        Ok(Reciprocal(self.args.len() - 1))
    }

    fn arg_columns(&self, r: Reciprocal) -> Result<usize, R1CSError> {
        self.args.get(r.0).map(|a| a.m).ok_or_else(|| gadget_error("unknown reciprocal argument"))
    }

    pub(super) fn reciprocal_term(&mut self, r: Reciprocal, num: LinearCombination<F>, tuple: &[LinearCombination<F>], c: Counts) -> Result<(), R1CSError> {
        let m = self.arg_columns(r)?;
        self.check_lc(&num, c)?;
        self.check_tuple(tuple, m, c)?;
        self.args[r.0].private.push((num, tuple.to_vec()));
        Ok(())
    }

    pub(super) fn reciprocal_public(&mut self, r: Reciprocal, coeff: LinearCombination<F>, row: &[u64], c: Counts) -> Result<(), R1CSError> {
        let m = self.arg_columns(r)?;
        self.check_lc(&coeff, c)?;
        if row.len() != m {
            return Err(gadget_error("public row length does not match the columns"));
        }
        self.args[r.0].public.push((coeff, row.to_vec()));
        Ok(())
    }

    /// The cost if finalized now, with `n` R1CS multipliers and `k` committed inputs.
    pub(super) fn cost(&self, n: usize, k: usize) -> Cost {
        let used = || self.tables.iter().filter(|t| !t.queries.is_empty());
        let n_w = self.n_w + used().map(|t| t.rows.len()).sum::<usize>();
        let n_p = self.args.iter().map(|a| a.private.len()).sum::<usize>() + used().map(|t| t.queries.len()).sum::<usize>();
        let n_prod = self.products.len();
        let n_r = if n == 0 && n_prod == 0 && n_p == 0 { 1 } else { n };
        // copies (spec §7.6): numerators and coefficients that read w_R, components of
        // tuples (m >= 2) that read w_L or w_R
        let right = |lc: &LinearCombination<F>| lc.terms.iter().any(|(x, _)| matches!(x, Variable::MultiplierRight(_)));
        let comp_copies = |m: usize, tuple: &[LinearCombination<F>]| if m >= 2 { tuple.iter().filter(|x| needs_early_copy(x)).count() } else { 0 };
        let copies: usize = self
            .args
            .iter()
            .map(|a| {
                a.private.iter().map(|(num, x)| right(num) as usize + comp_copies(a.m, x)).sum::<usize>()
                    + a.public.iter().filter(|(c, _)| right(c)).count()
            })
            .sum::<usize>()
            + used().map(|t| t.queries.iter().map(|q| comp_copies(t.m, q)).sum::<usize>()).sum::<usize>();
        let gates = n_p + n_r + n_prod;
        Cost {
            bp_phase1: n + (n_w + 1) / 2 + n_prod,
            bp_phase2: n_p,
            bppp_gates: gates,
            bppp_linear: (n_r + k + n_w + copies).saturating_sub(gates),
        }
    }

    /// Finalization (spec §7.4): one multiplicity witness per row of each table with lookups,
    /// and the tables appended to the arguments. With `eval` (the prover) returns the
    /// multiplicities, or an error for a lookup equal to no row. Constant time in the witness:
    /// `|T|` comparisons per lookup, or an oblivious sort for large tables.
    pub(super) fn finalize(&mut self, eval: Option<&dyn Fn(&LinearCombination<F>) -> F>) -> Result<Vec<F>, R1CSError> {
        // arguments without terms add nothing (spec §7.4)
        self.args.retain(|a| !a.private.is_empty() || !a.public.is_empty());
        let mut values = Vec::new();
        #[cfg(test)]
        let cheat: Option<Vec<F>> = if eval.is_some() { cheat::get().multiplicities.map(|m| m.iter().map(cheat::to_field).collect()) } else { None };
        #[cfg(not(test))]
        let cheat: Option<Vec<F>> = None;
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
                    let rows: Vec<Vec<F>> = table.rows.iter().map(|r| r.iter().map(|e| F::from(*e)).collect()).collect();
                    let mut m = vec![0u64; table.rows.len()];
                    let mut all_found = Choice::from(1u8);
                    for q in &table.queries {
                        let mut qv: Vec<F> = q.iter().map(|lc| eval(lc)).collect();
                        let mut found = Choice::from(0u8);
                        for (r, row) in rows.iter().enumerate() {
                            let eq = qv.iter().zip(row).fold(Choice::from(1u8), |acc, (x, y)| acc & x.ct_eq(y));
                            m[r] += (eq & !found).unwrap_u8() as u64;
                            found |= eq;
                        }
                        all_found &= found;
                        qv.iter_mut().for_each(|x| x.zeroize());
                    }
                    (m, all_found)
                } else {
                    let key = |xs: &mut dyn Iterator<Item = F>| xs.flat_map(|x| x.to_bytes32()).collect::<Vec<u8>>();
                    let rows: Vec<Vec<u8>> = table.rows.iter().map(|r| key(&mut r.iter().map(|e| F::from(*e)))).collect();
                    let mut lookups: Vec<Vec<u8>> = table.queries.iter().map(|q| key(&mut q.iter().map(|lc| eval(lc)))).collect();
                    let out = super::oblivious::count(&rows, &lookups);
                    lookups.iter_mut().flatten().for_each(|b| *b = 0);
                    out
                };
                if !bool::from(all_found) && !super::cheats::unchecked() {
                    return Err(gadget_error("lookup query is not a table row"));
                }
                values.extend(m.into_iter().map(F::from));
            }
            let private = table.queries.into_iter().map(|q| (F::ONE.into(), q)).collect();
            let public = (0..table.rows.len())
                .zip(table.rows)
                .map(|(r, row)| (LinearCombination::from(Variable::Witness(first + r)) * (-F::ONE), row))
                .collect();
            self.args.push(Argument { m: table.m, private, public });
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

    /// A cheat value in the field of the proof (the cheats are ristretto255 scalars).
    pub(crate) fn to_field<F: crate::curve::Field>(x: &Scalar) -> F {
        F::from_bytes32(&crate::curve::Field::to_bytes32(x)).expect("a canonical scalar")
    }
}

/// The BP lowering of one argument (spec §7.5, a port of bpvm's `LogUp`): challenges `alpha`
/// (for tuples of two or more components) and `c`; one multiplier `r * d = num` with
/// `d = c + sum_j alpha^j x_j` per private term; `sum r + sum coeff / d(row) = 0`.
pub(super) fn logup<F: Field, CS: RandomizedConstraintSystem<F>>(cs: &mut CS, arg: Argument<F>) -> Result<(), R1CSError> {
    let m = arg.m;
    let alpha = if m > 1 { cs.challenge_scalar(b"logup alpha") } else { F::ONE };
    let c = cs.challenge_scalar(b"logup c");
    let pows: Vec<F> = core::iter::successors(Some(F::ONE), |p| Some(*p * alpha)).take(m).collect();
    let zero = || gadget_error("a reciprocal argument has a zero denominator");
    let compress = |x: Vec<LinearCombination<F>>| x.into_iter().zip(&pows).fold(LinearCombination::from(c), |acc, (lc, a)| acc + lc * *a);
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
            let d = row.iter().zip(&pows).fold(c, |acc, (e, a)| acc + F::from(*e) * a);
            den.iter_mut().filter(|x| x.is_some()).for_each(|x| *x = Some(d));
        }
        if let Some(v) = ch.numerator {
            num.iter_mut().filter(|x| x.is_some()).for_each(|x| *x = Some(cheat::to_field(&v)));
        }
    }
    let prover = den.iter().all(Option::is_some) && num.iter().all(Option::is_some) && !arg.private.is_empty();
    let mut inv: Option<Vec<F>> = if prover {
        let mut d: Vec<F> = den.iter().map(|x| x.unwrap()).collect();
        if d.iter().any(|x| *x == F::ZERO) {
            return Err(zero());
        }
        F::batch_invert(&mut d);
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
    let mut pub_den: Vec<F> =
        arg.public.iter().map(|(_, row)| row.iter().zip(&pows).fold(c, |acc, (e, a)| acc + F::from(*e) * a)).collect();
    if pub_den.iter().any(|x| *x == F::ZERO) {
        return Err(zero());
    }
    if !pub_den.is_empty() {
        F::batch_invert(&mut pub_den);
    }
    for ((coeff, _), w) in arg.public.into_iter().zip(pub_den) {
        sum = sum + coeff * w;
    }
    cs.constrain(sum);
    for x in den.iter_mut().chain(num.iter_mut()).flatten() {
        x.zeroize();
    }
    for x in inv.iter_mut().flatten() {
        x.zeroize();
    }
    Ok(())
}

/// Whether a tuple component reads `w_L` or `w_R` and so needs a copy into `C_O` before the
/// BP++ challenge `eta` (spec §7.6).
pub(super) fn needs_early_copy<F: Field>(lc: &LinearCombination<F>) -> bool {
    lc.terms.iter().any(|(x, _)| matches!(x, Variable::MultiplierLeft(_) | Variable::MultiplierRight(_)))
}

#[cfg(test)]
mod tests {
    use curve25519_dalek::scalar::Scalar;
    use super::*;

    type Builder = super::Builder<Scalar>;

    const C: Counts = Counts { n: 2, k: 1 };

    /// A builder with witnesses `W0..W3` and a one-column table of 16 rows.
    fn four() -> (Builder, TableId) {
        let mut b = Builder::default();
        for _ in 0..4 {
            b.witness();
        }
        let t = b.table((0..16).map(|x| vec![x]).collect()).unwrap();
        (b, t)
    }

    #[test]
    fn tables_are_validated() {
        let mut b = Builder::default();
        assert!(b.table(vec![vec![]]).is_err(), "no column");
        assert!(b.table(Vec::<Vec<u64>>::new()).is_err(), "empty");
        assert!(b.table(vec![vec![1], vec![1, 2]]).is_err(), "row length");
        assert!(b.table(vec![vec![1, 2], vec![1]]).is_err(), "row length");
        assert!(b.table(vec![vec![u64::MAX, 0, 7]]).is_ok());
        assert!(b.table(vec![vec![256], vec![256]]).is_ok(), "duplicate rows");
        assert_eq!(b.tables.len(), 2);
        assert_eq!(b.tables[0].m, 3);
    }

    /// No bounds (spec §7.3): any component, negative or huge coefficients, unbounded
    /// witnesses, constants, products' wires.
    #[test]
    fn tuple_components_need_no_bound() {
        let (mut b, _) = four();
        let (w0, w2) = (Variable::Witness(0), Variable::Witness(2));
        let t2 = b.table(vec![vec![0, 0]]).unwrap();
        assert!(b.lookup(t2, &[w2.into(), w0.into()], C).is_ok());
        assert!(b.lookup(t2, &[w0 * (-Scalar::ONE), Scalar::from(1u128 << 100).into()], C).is_ok());
        assert!(b.lookup(t2, &[Variable::MultiplierLeft(1).into(), Variable::MultiplierRight(0) - w0], C).is_ok());
        assert_eq!(b.tables[1].queries.len(), 3);
    }

    #[test]
    fn variables_must_exist() {
        let (mut b, t) = four();
        assert!(b.lookup(t, &[Variable::Witness(4).into()], C).is_err());
        assert!(b.lookup(t, &[Variable::MultiplierRight(2).into()], C).is_err());
        assert!(b.lookup(t, &[Variable::MultiplierOutput(1).into()], C).is_ok());
        assert!(b.lookup(t, &[Variable::Committed(1).into()], C).is_err());
        assert!(b.constrain_product(Variable::Witness(9).into(), Scalar::ONE.into(), Scalar::ONE.into(), C).is_err());
        assert!(b.lookup(TableId(7), &[Scalar::ONE.into()], C).is_err());
        assert!(b.lookup(t, &[Scalar::ONE.into(), Scalar::ONE.into()], C).is_err(), "tuple length");
        assert!(b.lookup(t, &[], C).is_err(), "tuple length");
        let before = b.tables[t.0].queries.len();
        assert!(b.lookup(t, &[Variable::Witness(4).into()], C).is_err());
        assert_eq!(b.tables[t.0].queries.len(), before, "a failed operation records nothing");
        let t2 = b.table(vec![vec![0, 0]]).unwrap();
        assert!(b.check_value_table(t2).is_err(), "lookup_value needs one column");
        assert!(b.check_value_table(t).is_ok());
    }

    #[test]
    fn reciprocals_are_validated() {
        let (mut b, _) = four();
        let (w0, w1, w2) = (Variable::Witness(0), Variable::Witness(1), Variable::Witness(2));
        let one = || LinearCombination::from(Scalar::ONE);
        let r = b.reciprocal(2).unwrap();
        assert!(b.reciprocal_term(r, one(), &[w0.into(), w1.into()], C).is_ok());
        assert!(b.reciprocal_public(r, w2.into(), &[15, 1 << 40], C).is_ok());
        assert!(b.reciprocal_public(r, one(), &[1], C).is_err(), "row length");
        assert!(b.reciprocal_term(r, -one(), &[w2.into()], C).is_err(), "tuple length");
        assert!(b.reciprocal_term(r, Variable::Witness(8).into(), &[w0.into(), w1.into()], C).is_err(), "unknown numerator variable");
        assert!(b.reciprocal_term(r, one(), &[w0.into(), Variable::Witness(8).into()], C).is_err(), "unknown component variable");
        assert!(b.reciprocal_public(r, Variable::Witness(8).into(), &[1, 2], C).is_err(), "unknown coefficient variable");
        assert_eq!((b.args[r.0].private.len(), b.args[r.0].public.len()), (1, 1), "a failed term records nothing");
        let x = b.reciprocal(1).unwrap();
        assert!(b.reciprocal_term(x, w2.into(), &[w2 * Scalar::from(7u64) + Scalar::ONE], C).is_ok());
        assert!(b.reciprocal_term(Reciprocal(9), one(), &[w0.into()], C).is_err(), "unknown argument");
        let _empty = b.reciprocal(3).unwrap();
        assert!(b.reciprocal(0).is_err(), "no column");
        assert_eq!(b.args.len(), 3);
        b.finalize(None).unwrap();
        assert_eq!(b.args.len(), 2, "an argument without terms is dropped");
    }

    #[test]
    fn finalize_counts_first_equal_row() {
        let mut b = Builder::default();
        let w: Vec<Variable> = (0..3).map(|_| b.witness()).collect();
        let t = b.table(vec![vec![1], vec![2], vec![1]]).unwrap();
        let _unused = b.table(vec![vec![0]]).unwrap();
        for x in &w {
            b.lookup(t, &[(*x).into()], C).unwrap();
        }
        let vals = [Scalar::from(1u64), Scalar::from(2u64), Scalar::from(1u64)];
        let eval = |lc: &LinearCombination<Scalar>| {
            lc.terms.iter().map(|(x, c)| c * if let Variable::Witness(i) = x { vals[*i] } else { Scalar::ONE }).sum()
        };
        let cost = b.cost(0, 0);
        let m = b.finalize(Some(&eval)).unwrap();
        assert_eq!(m, vec![Scalar::from(2u64), Scalar::ONE, Scalar::ZERO]);
        assert_eq!(b.n_w, 6, "multiplicities of used tables only");
        assert_eq!(b.args.len(), 1);
        assert_eq!(b.args[0].public[0].0, LinearCombination::from(Variable::Witness(3)) * (-Scalar::ONE));
        assert_eq!(cost, Cost { bp_phase1: 3, bp_phase2: 3, bppp_gates: 3, bppp_linear: 3 });
        // a query equal to no row
        let mut b = Builder::default();
        let x = b.witness();
        let t = b.table(vec![vec![1]]).unwrap();
        b.lookup(t, &[x.into()], C).unwrap();
        let zero = |_: &LinearCombination<Scalar>| Scalar::ZERO;
        assert!(b.finalize(Some(&zero)).is_err());
    }

    /// Copies are counted for tuple components that read `w_L` or `w_R` (m >= 2), lookups of
    /// tables included, not for one-component tuples (spec §7.6).
    #[test]
    fn cost_counts_component_copies() {
        let (l, r, o) = (Variable::MultiplierLeft(0), Variable::MultiplierRight(1), Variable::MultiplierOutput(0));
        let mut b = Builder::default();
        let t1 = b.table(vec![vec![0]]).unwrap();
        b.lookup(t1, &[l.into()], C).unwrap();
        let base = b.cost(2, 1);
        let t2 = b.table(vec![vec![0, 0]]).unwrap();
        b.lookup(t2, &[l.into(), o + Scalar::ONE], C).unwrap();
        let one = b.cost(2, 1);
        // + 1 pole, + 1 multiplicity, + 1 copy (l); o needs none
        assert_eq!(one.bppp_gates, base.bppp_gates + 1);
        assert_eq!(one.bppp_linear, base.bppp_linear + 1 + 1 - 1);
        let x = b.reciprocal(2).unwrap();
        b.reciprocal_term(x, r.into(), &[r.into(), l + r], C).unwrap();
        let two = b.cost(2, 1);
        // + 1 pole, + 3 copies (numerator r, both components)
        assert_eq!(two.bppp_gates, one.bppp_gates + 1);
        assert_eq!(two.bppp_linear, one.bppp_linear + 3 - 1);
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
            let range = b.table((0..8).map(|x| vec![x]).collect()).unwrap();
            let t = b.table(rows).unwrap();
            for x in &w {
                b.lookup(range, &[(*x).into()], C).unwrap();
            }
            for i in 0..n_w {
                b.lookup(t, &[w[2 * i].into(), w[2 * i + 1].into()], C).unwrap();
            }
            let eval = |lc: &LinearCombination<Scalar>| {
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
}

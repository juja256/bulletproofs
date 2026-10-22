//! The constraint system trait, and the randomized constraints the BP backend lowers lookups
//! and reciprocal arguments to.

use super::builder::{Cost, Reciprocal, TableId};
use super::{LinearCombination, R1CSError, Variable};

use crate::curve::Field;
use crate::transcript::TranscriptBackend;

/// The interface for a constraint system, abstracting over the prover and verifier's roles.
///
/// Statements to be proved by an [`R1CSProof`](crate::r1cs::R1CSProof) are specified by
/// programmatically constructing constraints. These constraints need to be identical between
/// the prover and verifier, since the prover and verifier need to construct the same
/// statement: gadgets are written once against this trait (with `F` the scalar field, or
/// generic over [`Field`] to run on every curve).
///
/// `multiply` and `constrain` are R1CS multipliers and constraints, as upstream; the builder
/// operations (witnesses, products, lookups, reciprocal arguments) are recorded independently
/// of the backend. All are lowered when the proof is made or checked: to Bulletproofs (BP,
/// spec §7.5) or to a Bulletproofs++ reciprocal form circuit (BP++, §7.6). Every variable an
/// operation reads must exist.
pub trait ConstraintSystem<F: Field> {
    /// Leases the proof transcript to the user, so they can add extra data to which the proof
    /// must be bound, but which is not available before creation of the constraint system
    /// (`merlin::Transcript`, `Sha256Transcript` or any other [`TranscriptBackend`], behind
    /// its interface).
    fn transcript(&mut self) -> &mut dyn TranscriptBackend;

    /// A free witness: `v` is the prover's value (`None` for the verifier).
    fn witness(&mut self, v: Option<F>) -> Result<Variable, R1CSError>;

    /// The product `left * right` as a new variable. A free witness that is the whole of
    /// `left` or `right` (coefficient 1, no constant) becomes the product's input wire, the first
    /// time it is one: it then costs nothing of its own.
    fn multiply(&mut self, left: LinearCombination<F>, right: LinearCombination<F>) -> Result<Variable, R1CSError>;

    /// The constraint `l * r = out`, without a new variable. Free witnesses fold into its input
    /// wires as for [`multiply`](Self::multiply).
    fn constrain_product(&mut self, l: LinearCombination<F>, r: LinearCombination<F>, out: LinearCombination<F>) -> Result<(), R1CSError>;

    /// The constraint `lc = 0`.
    fn constrain(&mut self, lc: LinearCombination<F>);

    /// The value of `lc`: `Some` for the prover, `None` for the verifier.
    fn eval(&self, lc: &LinearCombination<F>) -> Option<F>;

    /// A public table: at least one row, all rows of the same length `m >= 1` (the columns).
    fn table(&mut self, rows: Vec<Vec<u64>>) -> Result<TableId, R1CSError>;

    /// Assert that `tuple` (`m` components) is a row of table `t`, component by component; the
    /// components may be any field elements (spec §7.3: the backends compress tuples with a
    /// challenge, so the lookup itself bounds every component).
    fn lookup(&mut self, t: TableId, tuple: &[LinearCombination<F>]) -> Result<(), R1CSError>;

    /// A witness that is an entry of the one-column table `t`.
    fn lookup_value(&mut self, t: TableId, v: Option<u64>) -> Result<Variable, R1CSError>;

    /// A new reciprocal argument over tuples of `m >= 1` components; add its terms with the
    /// methods of [`Reciprocal`].
    fn reciprocal(&mut self, m: usize) -> Result<Reciprocal, R1CSError>;

    /// Add the term `num / (X + tuple)` to the argument `r` (`tuple` has `m` components).
    fn reciprocal_term(&mut self, r: Reciprocal, num: LinearCombination<F>, tuple: &[LinearCombination<F>]) -> Result<(), R1CSError>;

    /// Add the term `coeff / (X + row)` for a public row (`m` entries) to the argument `r`.
    fn reciprocal_public(&mut self, r: Reciprocal, coeff: LinearCombination<F>, row: &[u64]) -> Result<(), R1CSError>;

    /// The cost of the circuit recorded so far, on both backends.
    fn cost(&self) -> Cost;
}

/// A constraint system that can defer constraints to a second phase with challenges (upstream
/// dalek's randomized constraints). Internal: the BP backend lowers lookups and reciprocal
/// arguments to it (logUp, spec §7.5); BP++ and the Simplicity compiler refuse it.
pub(crate) trait RandomizableConstraintSystem<F: Field>: ConstraintSystem<F> {
    /// The constraint system of the second phase.
    type RandomizedCS: RandomizedConstraintSystem<F>;

    /// Defer `callback` until every first-phase variable is committed; it then draws
    /// challenges bound to them.
    fn specify_randomized_constraints<CB>(&mut self, callback: CB) -> Result<(), R1CSError>
    where
        CB: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>;
}

/// The second phase: BP multipliers and linear constraints, and challenges.
pub(crate) trait RandomizedConstraintSystem<F: Field> {
    /// A multiplier with `left = l`, `right = r`; returns `(left, right, out)` (upstream's
    /// gadgets in `r1cs::tests`; logUp needs only free multipliers).
    #[allow(dead_code)]
    fn multiply(&mut self, l: LinearCombination<F>, r: LinearCombination<F>) -> (Variable, Variable, Variable);

    /// A multiplier with free inputs (the prover's values); returns `(left, right, out)`.
    fn allocate_multiplier(&mut self, input_assignments: Option<(F, F)>) -> Result<(Variable, Variable, Variable), R1CSError>;

    /// The constraint `lc = 0`.
    fn constrain(&mut self, lc: LinearCombination<F>);

    /// The value of `lc`: `Some` for the prover, `None` for the verifier.
    fn eval(&self, lc: &LinearCombination<F>) -> Option<F>;

    /// A challenge bound to every first-phase variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> F;
}

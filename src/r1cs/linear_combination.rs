//! Definition of linear combinations.

use curve25519_dalek::scalar::Scalar;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

use crate::curve::Field;

/// A variable of a constraint system: an input committed with `commit`, a witness, the
/// product returned by `multiply`, or the constant [`Variable::ONE`]. Variables are made by
/// the constraint system and belong to it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Variable(pub(crate) Var);

impl Variable {
    /// The constant 1.
    pub const ONE: Variable = Variable(Var::One);
}

/// The kinds of variables, private to the backends.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Var {
    /// An external input specified by a commitment.
    Committed(usize),
    /// The left input of a multiplication gate.
    MultiplierLeft(usize),
    /// The right input of a multiplication gate.
    MultiplierRight(usize),
    /// The output of a multiplication gate.
    MultiplierOutput(usize),
    /// A witness (spec §7): folded into a product's input wire, or free (half a multiplier in
    /// BP, a slot of `w_O` in BP++).
    Witness(usize),
    /// The constant 1.
    One,
}

impl<F: Field> LinearCombination<F> {
    /// Takes a linear combination and returns a simplified version, combining the terms of
    /// each variable.
    pub fn simplify(&self) -> LinearCombination<F> {
        let mut vars: HashMap<Variable, F> = HashMap::new();

        for (var, val) in &self.terms {
            *vars.entry(*var).or_insert(F::ZERO) += val;
        }

        let mut new_lc_terms = vec![];
        for (var, val) in vars {
            new_lc_terms.push((var, val));
        }
        new_lc_terms.iter().collect()
    }
}

/// `v` as a linear combination over `F`: the way to start arithmetic on variables, `lc(a) + b`
/// (a variable names no field, so two variables or a variable and an integer do not add).
pub fn lc<F: Field>(v: impl Into<LinearCombination<F>>) -> LinearCombination<F> {
    v.into()
}

impl<F: Field> From<Variable> for LinearCombination<F> {
    fn from(v: Variable) -> LinearCombination<F> {
        LinearCombination { terms: vec![(v, F::ONE)] }
    }
}

impl<F: Field> From<F> for LinearCombination<F> {
    fn from(s: F) -> LinearCombination<F> {
        LinearCombination { terms: vec![(Variable::ONE, s)] }
    }
}


// Arithmetic on a variable produces a linear combination when the other operand names the
// field (a linear combination or a field element).

impl<F: Field> Add<LinearCombination<F>> for Variable {
    type Output = LinearCombination<F>;

    fn add(self, other: LinearCombination<F>) -> Self::Output {
        LinearCombination::from(self) + other
    }
}

impl<F: Field> Sub<LinearCombination<F>> for Variable {
    type Output = LinearCombination<F>;

    fn sub(self, other: LinearCombination<F>) -> Self::Output {
        LinearCombination::from(self) - other
    }
}

impl<F: Field> Add<F> for Variable {
    type Output = LinearCombination<F>;

    fn add(self, other: F) -> Self::Output {
        LinearCombination::from(self) + other
    }
}

impl<F: Field> Sub<F> for Variable {
    type Output = LinearCombination<F>;

    fn sub(self, other: F) -> Self::Output {
        LinearCombination::from(self) - other
    }
}

impl<F: Field> Mul<F> for Variable {
    type Output = LinearCombination<F>;

    fn mul(self, other: F) -> Self::Output {
        LinearCombination { terms: vec![(self, other)] }
    }
}

// Arithmetic on scalars with variables produces linear combinations (a foreign type on the
// left takes one impl per field: ristretto255's here, secp256k1's in `curve::secp256k1`)

impl Add<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(Variable::ONE, self), (other, Scalar::ONE)] }
    }
}

impl Sub<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn sub(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(Variable::ONE, self), (other, -Scalar::ONE)] }
    }
}

impl Mul<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn mul(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(other, self)] }
    }
}

/// Represents a linear combination of
/// [`Variables`](crate::r1cs::Variable).  Each term is represented by a
/// `(Variable, F)` pair.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearCombination<F: Field> {
    pub(super) terms: Vec<(Variable, F)>,
}

impl<F: Field> Default for LinearCombination<F> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl<F: Field> FromIterator<(Variable, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable, F)>,
    {
        LinearCombination { terms: iter.into_iter().collect() }
    }
}

impl<'a, F: Field> FromIterator<&'a (Variable, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable, F)>,
    {
        LinearCombination { terms: iter.into_iter().cloned().collect() }
    }
}

// Arithmetic on linear combinations

impl<F: Field, L: Into<LinearCombination<F>>> Add<L> for LinearCombination<F> {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().cloned());
        LinearCombination { terms: self.terms }
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Sub<L> for LinearCombination<F> {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().map(|(var, coeff)| (*var, -*coeff)));
        LinearCombination { terms: self.terms }
    }
}

impl Mul<LinearCombination<Scalar>> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn mul(self, other: LinearCombination<Scalar>) -> Self::Output {
        other * self
    }
}

impl<F: Field> Neg for LinearCombination<F> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -*s
        }
        self
    }
}

impl<F: Field> Mul<F> for LinearCombination<F> {
    type Output = Self;

    fn mul(mut self, other: F) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}

/// Integer constants of every width in linear combinations, as upstream
/// (`From<S: Into<Scalar>>`).
macro_rules! integer_constants {
    ($($t:ty),*) => {$(
        impl<F: Field> From<$t> for LinearCombination<F> {
            fn from(s: $t) -> LinearCombination<F> {
                LinearCombination { terms: vec![(Variable::ONE, crate::util::from_u128(s as u128))] }
            }
        }

        impl<F: Field> Mul<$t> for LinearCombination<F> {
            type Output = Self;

            fn mul(self, other: $t) -> Self::Output {
                self * crate::util::from_u128::<F>(other as u128)
            }
        }



    )*};
}

integer_constants!(u8, u16, u32, u64, u128);

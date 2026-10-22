//! Definition of linear combinations.

use curve25519_dalek::scalar::Scalar;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

use crate::curve::Field;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variable {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// A witness of the circuit builder (spec §7): half a multiplier in BP, a slot of `w_O`
    /// in BP++.
    Witness(usize),
    /// Represents the constant 1.
    One(),
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

/// `v` as a linear combination over `F`: the way to start arithmetic on variables in code
/// generic over the field, where `a + b` of two [`Variable`]s (ristretto255 only) does not
/// apply: `lc(a) + b`.
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
        LinearCombination { terms: vec![(Variable::One(), s)] }
    }
}


// Arithmetic on variables produces linear combinations: generic over the field when the
// other operand names it (a linear combination or a field element), over ristretto255's
// scalars otherwise (two variables, an integer), as before the curve became a parameter.

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

/// Two variables make a linear combination over ristretto255's scalars (the field cannot be
/// inferred from two variables; in generic code write `lc(a) + b`).
///
/// ```
/// use bulletproofs::r1cs::{LinearCombination, Variable};
/// use curve25519_dalek::scalar::Scalar;
///
/// let (a, b) = (Variable::Committed(0), Variable::Committed(1));
/// let sum: LinearCombination<Scalar> = a + b;
/// assert_eq!(sum, LinearCombination::from(a) + LinearCombination::from(b));
/// ```
impl Add<Variable> for Variable {
    type Output = LinearCombination<Scalar>;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination::from(self) + other
    }
}

impl Sub<Variable> for Variable {
    type Output = LinearCombination<Scalar>;

    fn sub(self, other: Variable) -> Self::Output {
        LinearCombination::from(self) - other
    }
}


impl Neg for Variable {
    type Output = LinearCombination<Scalar>;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

// Arithmetic on scalars with variables produces linear combinations (a foreign type on the
// left takes one impl per field: ristretto255's here)

impl Add<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(Variable::One(), self), (other, Scalar::ONE)] }
    }
}

impl Sub<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn sub(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(Variable::One(), self), (other, -Scalar::ONE)] }
    }
}

impl Mul<Variable> for Scalar {
    type Output = LinearCombination<Scalar>;

    fn mul(self, other: Variable) -> Self::Output {
        LinearCombination { terms: vec![(other, self)] }
    }
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
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

/// Integer constants of every width, as upstream (`From<S: Into<Scalar>>`): generic for
/// linear combinations, ristretto255 with a variable on the left.
macro_rules! integer_constants {
    ($($t:ty),*) => {$(
        impl<F: Field> From<$t> for LinearCombination<F> {
            fn from(s: $t) -> LinearCombination<F> {
                LinearCombination { terms: vec![(Variable::One(), crate::util::from_u128(s as u128))] }
            }
        }

        impl<F: Field> Mul<$t> for LinearCombination<F> {
            type Output = Self;

            fn mul(self, other: $t) -> Self::Output {
                self * crate::util::from_u128::<F>(other as u128)
            }
        }

        impl Add<$t> for Variable {
            type Output = LinearCombination<Scalar>;

            fn add(self, other: $t) -> Self::Output {
                LinearCombination::from(self) + other
            }
        }

        impl Sub<$t> for Variable {
            type Output = LinearCombination<Scalar>;

            fn sub(self, other: $t) -> Self::Output {
                LinearCombination::from(self) - other
            }
        }

        impl Mul<$t> for Variable {
            type Output = LinearCombination<Scalar>;

            fn mul(self, other: $t) -> Self::Output {
                self * Scalar::from(other)
            }
        }
    )*};
}

integer_constants!(u8, u16, u32, u64, u128);

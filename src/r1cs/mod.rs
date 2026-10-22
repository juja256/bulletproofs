
mod notes {}

mod backend;
mod builder;
mod compact;
mod constraint_system;
mod linear_combination;
mod oblivious;
mod proof;
mod prover;
mod verifier;
#[cfg(test)]
mod soundness;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod vectors;

pub use self::backend::{Backend, UnknownBackend};

#[cfg(feature = "cheats")]
pub mod cheats;
#[cfg(not(feature = "cheats"))]
pub(crate) mod cheats;
pub use self::builder::{Cost, Reciprocal, TableId};
pub use self::constraint_system::ConstraintSystem;
pub(crate) use self::constraint_system::{RandomizableConstraintSystem, RandomizedConstraintSystem};
pub use self::linear_combination::{lc, LinearCombination, Variable};
pub(crate) use self::linear_combination::Var;
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::Verifier;

pub use crate::errors::R1CSError;

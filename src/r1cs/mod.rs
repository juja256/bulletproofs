#![cfg_attr(feature = "docs", doc(include = "../../docs/r1cs-docs-example.md"))]

#[cfg_attr(feature = "docs", doc(include = "../../docs/cs-proof.md"))]
mod notes {}

mod backend;
mod builder;
mod compact;
mod constraint_system;
mod linear_combination;
mod metrics;
mod oblivious;
mod proof;
mod prover;
mod verifier;
#[cfg(all(test, feature = "bppp"))]
mod soundness;
#[cfg(all(test, feature = "bppp"))]
mod vectors;

pub use self::backend::{Backend, UnknownBackend};

#[cfg(feature = "cheats")]
pub mod cheats;
#[cfg(not(feature = "cheats"))]
pub(crate) mod cheats;
pub use self::builder::{CircuitBuilder, Cost, Reciprocal, TableId};
pub use self::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
pub use self::linear_combination::{lc, LinearCombination, Variable};
pub use self::metrics::Metrics;
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::Verifier;

pub use crate::errors::R1CSError;

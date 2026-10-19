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

pub use self::backend::Backend;

/// Testing only (feature `cheats`): a prover that skips its own checks, so that downstream
/// soundness tests can check that the verifier rejects what it produces.
#[cfg(feature = "cheats")]
pub mod cheats {
    use core::cell::Cell;

    thread_local! {
        static UNCHECKED: Cell<bool> = Cell::new(false);
    }

    /// While on (in this thread), the prover counts multiplicities only for lookups that equal
    /// a row (instead of refusing the others) and the BP++ prover proves unsatisfied circuits
    /// (instead of refusing them). The BP prover already proves violated constraints. The
    /// verifier is unaffected: such proofs must not verify.
    pub fn set_unchecked_prover(on: bool) {
        UNCHECKED.with(|u| u.set(on));
    }

    pub(crate) fn unchecked() -> bool {
        UNCHECKED.with(|u| u.get())
    }
}

#[cfg(not(feature = "cheats"))]
pub(crate) mod cheats {
    pub(crate) fn unchecked() -> bool {
        false
    }
}
pub use self::builder::{CircuitBuilder, Cost, Reciprocal, TableId};
pub use self::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
pub use self::linear_combination::{LinearCombination, Variable};
pub use self::metrics::Metrics;
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::Verifier;

pub use crate::errors::R1CSError;

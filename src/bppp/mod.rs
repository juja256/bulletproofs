//! Bulletproofs++ (Eagen, Kanjalkar, Ruffing, Nick; ePrint 2022/510) on ristretto255.
//! The protocol as implemented is pinned in `docs/bppp/spec.md`.

#![allow(non_snake_case)]

pub(crate) mod batch;
pub(crate) mod circuit;
mod gens;
pub(crate) mod mact;
mod poly;
pub(crate) mod range;
pub(crate) mod reciprocal;
mod sparse;
pub(crate) mod terms;
#[cfg(test)]
pub(crate) mod testutil;
#[cfg(test)]
mod tuple_tests;
pub(crate) mod transcript;
pub(crate) mod wnla;

pub use self::batch::BatchVerifier;
pub use self::circuit::{ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
pub use self::gens::BpppGens;
pub(crate) use self::gens::capacity as gens_capacity;
pub use self::mact::{MactEntry, MactProof, MactStatement};
pub use self::range::{RangeProof, RangeStatement};
pub use self::reciprocal::{Component, LateWitness, Pole, ReciprocalCircuit, ReciprocalProof, ReciprocalRow, ReciprocalWitness, TuplePole};
pub use self::sparse::SparseMatrix;
pub use self::transcript::BpppTranscript;
pub use self::wnla::{WnlaProof, WnlaStatement};

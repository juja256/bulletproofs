//! Bulletproofs++ (Eagen, Kanjalkar, Ruffing, Nick; ePrint 2022/510) on ristretto255.
//! The protocol as implemented is pinned in `docs/bppp/spec.md`.

#![allow(non_snake_case)]

pub mod circuit;
mod gens;
mod poly;
pub mod reciprocal;
mod sparse;
mod transcript;
pub mod wnla;

pub use self::circuit::{ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
pub use self::gens::BpppGens;
pub use self::reciprocal::{ReciprocalCircuit, ReciprocalRow, ReciprocalWitness};
pub use self::sparse::SparseMatrix;
pub use self::transcript::BpppTranscript;
pub use self::wnla::{WnlaProof, WnlaStatement};

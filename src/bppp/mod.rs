//! Bulletproofs++ (Eagen, Kanjalkar, Ruffing, Nick; ePrint 2022/510) on ristretto255.
//! The protocol as implemented is pinned in `docs/bppp/spec.md`.

#![allow(non_snake_case)]

mod transcript;
pub mod wnla;

pub use self::transcript::BpppTranscript;
pub use self::wnla::{WnlaProof, WnlaStatement};

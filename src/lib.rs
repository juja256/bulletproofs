
extern crate alloc;

#[macro_use]
extern crate serde_derive;

mod util;

mod notes {
    mod inner_product_proof {}
    mod range_proof {}
    mod r1cs_proof {}
}

pub mod curve;
mod errors;
mod generators;
mod inner_product_proof;
mod linear_proof;
mod range_proof;
mod transcript;

pub use crate::curve::{Curve, Ristretto};
pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::linear_proof::LinearProof;
pub use crate::range_proof::RangeProof;
pub use crate::transcript::{TranscriptBackend, TranscriptRef};
pub use crate::transcript::Sha256Transcript;

pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

pub mod r1cs;

pub mod bppp;

pub mod elements;

#[cfg(feature = "simplicity")]
pub mod simplicity;


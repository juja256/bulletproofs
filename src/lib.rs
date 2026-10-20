#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "docs", feature(external_doc))]
#![cfg_attr(feature = "docs", deny(missing_docs))]
#![cfg_attr(feature = "docs", doc(include = "../README.md"))]
#![cfg_attr(
    feature = "docs",
    doc(html_root_url = "https://docs.rs/bulletproofs/5.0.0")
)]

extern crate alloc;

#[macro_use]
extern crate serde_derive;

mod util;

#[cfg_attr(feature = "docs", doc(include = "../docs/notes-intro.md"))]
mod notes {
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-ipp.md"))]
    mod inner_product_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-rp.md"))]
    mod range_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-r1cs.md"))]
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
pub use crate::transcript::TranscriptBackend;

#[cfg_attr(feature = "docs", doc(include = "../docs/aggregation-api.md"))]
pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

#[cfg(feature = "yoloproofs")]
#[cfg(feature = "std")]
pub mod r1cs;

#[cfg(feature = "bppp")]
pub mod bppp;

#[cfg(feature = "secp256k1")]
pub mod elements;

/// The proofs over secp256k1: the crate's types with the curve parameter set to
/// [`curve::Secp256k1`]. Generators come from `for_curve` (`new` and `default` are the
/// ristretto255 ones); `PedersenGens` has `B` = H of secp256k1-zkp and `B_blinding` = G.
///
/// A 64-bit Bulletproofs++ range proof:
///
/// ```
/// # #[cfg(feature = "bppp")]
/// # {
/// use bulletproofs::bppp::RangeStatement;
/// use bulletproofs::curve::ff::Field;
/// use bulletproofs::secp256k1::{bppp::RangeProof, BulletproofGens, PedersenGens, Scalar};
/// use merlin::Transcript;
///
/// let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
/// let pc = PedersenGens::for_curve();
/// let bp = BulletproofGens::for_curve(st.generators_capacity(), 1);
/// let blinding = Scalar::random(&mut rand::thread_rng());
/// let (proof, commitments) =
///     RangeProof::prove(&st, &pc, &bp, &[1234567], &[blinding], &mut Transcript::new(b"doc"), &mut rand::thread_rng())
///         .unwrap();
/// let bytes = proof.to_bytes();
/// let proof = RangeProof::from_bytes(&bytes, &st).unwrap();
/// assert!(proof.verify(&st, &pc, &bp, &commitments, &mut Transcript::new(b"doc")).is_ok());
/// # }
/// ```
#[cfg(feature = "secp256k1")]
pub mod secp256k1 {
    pub use crate::curve::{Secp256k1, Secp256k1Compressed};
    pub use crate::elements;

    /// A scalar (big-endian in proofs).
    pub type Scalar = k256::Scalar;
    /// A group element.
    pub type Point = k256::ProjectivePoint;
    /// Pedersen generators over secp256k1.
    pub type PedersenGens = crate::PedersenGens<Secp256k1>;
    /// Bulletproofs generators over secp256k1.
    pub type BulletproofGens = crate::BulletproofGens<Secp256k1>;
    /// A Bulletproofs range proof over secp256k1.
    pub type RangeProof = crate::RangeProof<Secp256k1>;
    /// A linear proof over secp256k1.
    pub type LinearProof = crate::LinearProof<Secp256k1>;

    /// R1CS and the circuit builder over secp256k1 (gadgets: `CircuitBuilder<Scalar>`).
    #[cfg(feature = "yoloproofs")]
    pub mod r1cs {
        use super::Secp256k1;

        /// The prover over secp256k1 (`Prover::new(&pc_gens, transcript)`).
        pub type Prover<'g, T> = crate::r1cs::Prover<'g, T, Secp256k1>;
        /// The verifier over secp256k1 (`Verifier::for_curve(transcript)`).
        pub type Verifier<T> = crate::r1cs::Verifier<T, Secp256k1>;
        /// An R1CS proof over secp256k1.
        pub type R1CSProof = crate::r1cs::R1CSProof<Secp256k1>;
        /// A linear combination over secp256k1's scalars.
        pub type LinearCombination = crate::r1cs::LinearCombination<k256::Scalar>;
    }

    /// Bulletproofs++ over secp256k1.
    #[cfg(feature = "bppp")]
    pub mod bppp {
        use super::Secp256k1;

        /// The circuit generators over secp256k1.
        pub type BpppGens<'a> = crate::bppp::BpppGens<'a, Secp256k1>;
        /// A BP++ range proof over secp256k1.
        pub type RangeProof = crate::bppp::RangeProof<Secp256k1>;
        /// A multi-asset transaction proof over secp256k1.
        pub type MactProof = crate::bppp::MactProof<Secp256k1>;
        /// A reciprocal form circuit proof over secp256k1.
        pub type ReciprocalProof = crate::bppp::ReciprocalProof<Secp256k1>;
        /// An arithmetic circuit proof over secp256k1.
        pub type CircuitProof = crate::bppp::CircuitProof<Secp256k1>;
    }
}

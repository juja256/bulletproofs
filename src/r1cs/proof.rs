#![allow(non_snake_case)]
//! Definition of the proof struct.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, IsIdentity};

use crate::errors::R1CSError;
use crate::inner_product_proof::InnerProductProof;
use crate::util;

use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

const ONE_PHASE_COMMITMENTS: u8 = 0;
const TWO_PHASE_COMMITMENTS: u8 = 1;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
///
/// Statements are specified by writing gadget functions which add
/// constraints to a [`ConstraintSystem`](::r1cs::ConstraintSystem)
/// implementation.  To construct an [`R1CSProof`], a prover constructs
/// a [`ProverCS`](::r1cs::ProverCS), then passes it to gadget
/// functions to build the constraint system, then consumes the
/// constraint system using
/// [`ProverCS::prove`](::r1cs::ProverCS::prove) to produce an
/// [`R1CSProof`].  To verify an [`R1CSProof`], a verifier constructs a
/// [`VerifierCS`](::r1cs::VerifierCS), then passes it to the same
/// gadget functions to (re)build the constraint system, then consumes
/// the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug)]
pub struct R1CSProof(pub(super) ProofKind);

/// The backend-specific content of an [`R1CSProof`].
#[derive(Clone, Debug)]
pub(super) enum ProofKind {
    /// A Bulletproofs proof; its encoding is unchanged from upstream.
    Bp(BpProof),
    /// A Bulletproofs++ proof of the lowered reciprocal form circuit (spec §6, §7.6), for every
    /// constraint system.
    #[cfg(feature = "bppp")]
    Bppp(BpppProof),
}

/// A Bulletproofs++ proof: the dimensions of the lowered reciprocal form circuit and its proof.
#[cfg(feature = "bppp")]
#[derive(Clone, Debug)]
pub(super) struct BpppProof {
    /// `N'_m = N_p + N_m`.
    pub(super) n_mm: usize,
    /// Length of the linear part, `N_lin`.
    pub(super) n_lin: usize,
    pub(super) proof: crate::bppp::CircuitProof,
}

/// Version tag of a BP++ proof (BP proofs use 0 and 1; 3 was the builder encoding before
/// spec §6 had one encoding).
#[cfg(feature = "bppp")]
const BPPP_V2: u8 = 2;

impl R1CSProof {
    /// Serializes the proof. A BP proof keeps the upstream encoding (see the BP layout below);
    /// a BP++ proof is the byte 2, `N'_m` and `N_lin` as `u64` little-endian, then the proof
    /// (spec §6.2).
    pub fn to_bytes(&self) -> Vec<u8> {
        match &self.0 {
            ProofKind::Bp(p) => p.to_bytes(),
            #[cfg(feature = "bppp")]
            ProofKind::Bppp(p) => {
                let mut out = alloc::vec![BPPP_V2];
                out.extend_from_slice(&(p.n_mm as u64).to_le_bytes());
                out.extend_from_slice(&(p.n_lin as u64).to_le_bytes());
                out.extend(p.proof.to_bytes());
                out
            }
        }
    }

    /// Returns the size in bytes required to serialize the proof.
    pub fn serialized_size(&self) -> usize {
        match &self.0 {
            ProofKind::Bp(p) => p.serialized_size(),
            #[cfg(feature = "bppp")]
            ProofKind::Bppp(_) => self.to_bytes().len(),
        }
    }

    /// Deserializes a proof of either backend.
    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof, R1CSError> {
        #[cfg(feature = "bppp")]
        {
            let tag = slice.first().copied();
            if tag == Some(BPPP_V2) {
                if slice.len() < 17 {
                    return Err(R1CSError::FormatError);
                }
                use core::convert::{TryFrom, TryInto};
                let u = |b: &[u8]| usize::try_from(u64::from_le_bytes(b.try_into().unwrap())).map_err(|_| R1CSError::FormatError);
                let (a, b) = (u(&slice[1..9])?, u(&slice[9..17])?);
                let proof = super::backend::proof_from_bytes_shape(&slice[17..], a, b)?;
                return Ok(R1CSProof(ProofKind::Bppp(BpppProof { n_mm: a, n_lin: b, proof })));
            }
        }
        BpProof::from_bytes(slice).map(|p| R1CSProof(ProofKind::Bp(p)))
    }
}

/// The Bulletproofs content of an [`R1CSProof`] (upstream encoding).
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub(super) struct BpProof {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: CompressedRistretto,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: CompressedRistretto,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: CompressedRistretto,
    /// Commitment to the values of input wires in the second phase.
    pub(super) A_I2: CompressedRistretto,
    /// Commitment to the values of output wires in the second phase.
    pub(super) A_O2: CompressedRistretto,
    /// Commitment to the blinding factors in the second phase.
    pub(super) S2: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub(super) ipp_proof: InnerProductProof,
}

impl BpProof {
    /// Serializes the proof into a byte array of 1 version byte + \\((13 or 16) + 2k\\) 32-byte elements,
    /// where \\(k=\lceil \log_2(n) \rceil\\) and \\(n\\) is the number of multiplication gates.
    ///
    /// # Layout
    ///
    /// The layout of the r1cs proof encoding is:
    /// * 1 version byte indicating whether the proof contains second-phase commitments or not,
    /// * 8 or 11 compressed Ristretto points \\(A_{I1},A_{O1},S_1,(A_{I2},A_{O2},S_2),T_1,...,T_6\\)
    ///   (\\(A_{I2},A_{O2},S_2\\) are skipped if there were no multipliers added in the randomized phase),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(k\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{k-1},R_{k-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        if self.missing_phase2_commitments() {
            buf.push(ONE_PHASE_COMMITMENTS);
            buf.extend_from_slice(self.A_I1.as_bytes());
            buf.extend_from_slice(self.A_O1.as_bytes());
            buf.extend_from_slice(self.S1.as_bytes());
        } else {
            buf.push(TWO_PHASE_COMMITMENTS);
            buf.extend_from_slice(self.A_I1.as_bytes());
            buf.extend_from_slice(self.A_O1.as_bytes());
            buf.extend_from_slice(self.S1.as_bytes());
            buf.extend_from_slice(self.A_I2.as_bytes());
            buf.extend_from_slice(self.A_O2.as_bytes());
            buf.extend_from_slice(self.S2.as_bytes());
        }
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_3.as_bytes());
        buf.extend_from_slice(self.T_4.as_bytes());
        buf.extend_from_slice(self.T_5.as_bytes());
        buf.extend_from_slice(self.T_6.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Returns the size in bytes required to serialize the `R1CSProof`.
    pub fn serialized_size(&self) -> usize {
        // version tag + (11 or 14) elements + the ipp
        let elements = if self.missing_phase2_commitments() {
            11
        } else {
            14
        };
        1 + elements * 32 + self.ipp_proof.serialized_size()
    }

    fn missing_phase2_commitments(&self) -> bool {
        self.A_I2.is_identity() && self.A_O2.is_identity() && self.S2.is_identity()
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<BpProof, R1CSError> {
        if slice.len() < 1 {
            return Err(R1CSError::FormatError);
        }
        let version = slice[0];
        let mut slice = &slice[1..];

        if slice.len() % 32 != 0 {
            return Err(R1CSError::FormatError);
        }

        let minlength = match version {
            ONE_PHASE_COMMITMENTS => 11 * 32,
            TWO_PHASE_COMMITMENTS => 14 * 32,
            _ => return Err(R1CSError::FormatError),
        };

        if slice.len() < minlength {
            return Err(R1CSError::FormatError);
        }

        // This macro takes care of counting bytes in the slice
        macro_rules! read32 {
            () => {{
                let tmp = util::read32(slice);
                slice = &slice[32..];
                tmp
            }};
        }

        let A_I1 = CompressedRistretto(read32!());
        let A_O1 = CompressedRistretto(read32!());
        let S1 = CompressedRistretto(read32!());
        let (A_I2, A_O2, S2) = if version == ONE_PHASE_COMMITMENTS {
            (
                CompressedRistretto::identity(),
                CompressedRistretto::identity(),
                CompressedRistretto::identity(),
            )
        } else {
            (
                CompressedRistretto(read32!()),
                CompressedRistretto(read32!()),
                CompressedRistretto(read32!()),
            )
        };
        let T_1 = CompressedRistretto(read32!());
        let T_3 = CompressedRistretto(read32!());
        let T_4 = CompressedRistretto(read32!());
        let T_5 = CompressedRistretto(read32!());
        let T_6 = CompressedRistretto(read32!());
        let t_x =
            Option::from(Scalar::from_canonical_bytes(read32!())).ok_or(R1CSError::FormatError)?;
        let t_x_blinding =
            Option::from(Scalar::from_canonical_bytes(read32!())).ok_or(R1CSError::FormatError)?;
        let e_blinding =
            Option::from(Scalar::from_canonical_bytes(read32!())).ok_or(R1CSError::FormatError)?;

        // XXX: IPPProof from_bytes gives ProofError.
        let ipp_proof = InnerProductProof::from_bytes(slice).map_err(|_| R1CSError::FormatError)?;

        Ok(BpProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T_1,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

impl Serialize for R1CSProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for R1CSProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct R1CSProofVisitor;

        impl<'de> Visitor<'de> for R1CSProofVisitor {
            type Value = R1CSProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid R1CSProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<R1CSProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return R1CSProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return R1CSProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(R1CSProofVisitor)
    }
}

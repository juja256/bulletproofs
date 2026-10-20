//! The transcript interface: [`TranscriptBackend`] (the core every protocol uses, implemented
//! by `merlin::Transcript`) and `TranscriptProtocol` (the protocols' messages on top of it).

use merlin::Transcript;

#[cfg(feature = "sha256-transcript")]
mod sha256;
#[cfg(feature = "sha256-transcript")]
pub use self::sha256::Sha256Transcript;

use crate::curve::{Curve, Field, PointEncoding};
use crate::errors::ProofError;

/// The core of a Fiat–Shamir transcript: what every protocol of the crate needs. Implemented
/// by `merlin::Transcript` (the default, the upstream transcripts); any other implementation
/// works wherever the crate takes a transcript. Object safe, so that a constraint system can
/// lease its transcript as `&mut dyn TranscriptBackend`; the MPC dealer also needs `Clone`.
pub trait TranscriptBackend {
    /// Absorb a labeled message.
    fn append_message(&mut self, label: &'static [u8], message: &[u8]);
    /// Absorb a labeled integer.
    fn append_u64(&mut self, label: &'static [u8], x: u64);
    /// Fill `dest` with challenge bytes bound to everything absorbed so far.
    fn challenge_bytes(&mut self, label: &'static [u8], dest: &mut [u8]);
    /// The start of the prover's RNG, bound to the transcript (never used by a verifier to
    /// compute a challenge).
    fn build_rng(&self) -> merlin::TranscriptRngBuilder;
}

impl TranscriptBackend for Transcript {
    fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        Transcript::append_message(self, label, message)
    }

    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        Transcript::append_u64(self, label, x)
    }

    fn challenge_bytes(&mut self, label: &'static [u8], dest: &mut [u8]) {
        Transcript::challenge_bytes(self, label, dest)
    }

    fn build_rng(&self) -> merlin::TranscriptRngBuilder {
        Transcript::build_rng(self)
    }
}

/// Something that holds a transcript: the transcript itself or a mutable borrow of it. The
/// R1CS prover and verifier take either (upstream took `BorrowMut<merlin::Transcript>`).
/// Every `&mut X` holds its `X`; the crate's transcripts also hold themselves, and so can
/// any other type with its own impl.
pub trait TranscriptRef {
    /// The transcript held.
    type Backend: TranscriptBackend;
    /// The transcript, mutably.
    fn backend(&mut self) -> &mut Self::Backend;
    /// The transcript.
    fn backend_ref(&self) -> &Self::Backend;
}

impl<'a, X: TranscriptBackend> TranscriptRef for &'a mut X {
    type Backend = X;
    fn backend(&mut self) -> &mut X {
        self
    }
    fn backend_ref(&self) -> &X {
        self
    }
}

impl TranscriptRef for Transcript {
    type Backend = Self;
    fn backend(&mut self) -> &mut Self {
        self
    }
    fn backend_ref(&self) -> &Self {
        self
    }
}

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append the curve for every curve but ristretto255 (whose transcripts stay those of the
    /// upstream crate), so that a proof is bound to its curve.
    fn curve_domain_sep<C: Curve>(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar<S: Field>(&mut self, label: &'static [u8], scalar: &S);

    /// Append a `point` with the given `label`.
    fn append_point<P: PointEncoding>(&mut self, label: &'static [u8], point: &P);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point<P: PointEncoding>(
        &mut self,
        label: &'static [u8],
        point: &P,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar<S: Field>(&mut self, label: &'static [u8]) -> S;
}

impl<T: TranscriptBackend + ?Sized> TranscriptProtocol for T {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-2phase");
    }

    fn curve_domain_sep<C: Curve>(&mut self) {
        if C::NAME != "ristretto255" {
            self.append_message(b"curve", C::NAME.as_bytes());
        }
    }

    fn append_scalar<S: Field>(&mut self, label: &'static [u8], scalar: &S) {
        self.append_message(label, &scalar.to_bytes32());
    }

    fn append_point<P: PointEncoding>(&mut self, label: &'static [u8], point: &P) {
        self.append_message(label, point.as_bytes());
    }

    fn validate_and_append_point<P: PointEncoding>(
        &mut self,
        label: &'static [u8],
        point: &P,
    ) -> Result<(), ProofError> {
        if point.is_identity() {
            Err(ProofError::VerificationError)
        } else {
            Ok(self.append_message(label, point.as_bytes()))
        }
    }

    fn challenge_scalar<S: Field>(&mut self, label: &'static [u8]) -> S {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        S::from_wide(&buf)
    }
}

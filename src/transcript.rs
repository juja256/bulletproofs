//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

use merlin::Transcript;

use crate::curve::{Curve, Field, PointEncoding};
use crate::errors::ProofError;

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

impl TranscriptProtocol for Transcript {
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

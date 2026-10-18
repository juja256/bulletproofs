#![allow(non_snake_case)]

use clear_on_drop::clear::Clear;
use core::borrow::BorrowMut;
use core::mem;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};

use super::{
    ConstraintSystem, LinearCombination, R1CSProof, RandomizableConstraintSystem,
    RandomizedConstraintSystem, Variable,
};

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::r1cs::Metrics;
use crate::transcript::TranscriptProtocol;
use crate::util;
use super::compact::{ConstraintStore, Flattened};

/// A [`ConstraintSystem`] implementation for use by the prover.
///
/// The prover commits high-level variables and their blinding factors `(v, v_blinding)`,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the proving code calls `prove`
/// which consumes the `Prover` instance, samples random challenges
/// that instantiate the randomized constraints, and creates a complete proof.
pub struct Prover<'g, T: BorrowMut<Transcript>> {
    transcript: T,
    pc_gens: &'g PedersenGens,
    /// The constraints accumulated so far.
    constraints: ConstraintStore,
    /// Secret data
    secrets: Secrets,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingProver<'g, T>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

/// Separate struct to implement Drop trait for (for zeroing),
/// so that compiler does not prohibit us from moving the Transcript out of `prove()`.
struct Secrets {
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<Scalar>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<Scalar>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<Scalar>,
    /// High-level witness data (value openings to V commitments)
    v: Vec<Scalar>,
    /// High-level witness data (blinding openings to V commitments)
    v_blinding: Vec<Scalar>,
}

/// Prover in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingProver<'g, T: BorrowMut<Transcript>> {
    prover: Prover<'g, T>,
}

/// Overwrite secrets with null bytes when they go out of scope.
impl Drop for Secrets {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.clear();

        // Important: due to how ClearOnDrop auto-implements InitializableFromZeroed
        // for T: Default, calling .clear() on Vec compiles, but does not
        // clear the content. Instead, it only clears the Vec's header.
        // Clearing the underlying buffer item-by-item will do the job, but will
        // keep the header as-is, which is fine since the header does not contain secrets.
        for e in self.a_L.iter_mut() {
            e.clear();
        }
        for e in self.a_R.iter_mut() {
            e.clear();
        }
        for e in self.a_O.iter_mut() {
            e.clear();
        }
        // XXX use ClearOnDrop instead of doing the above
    }
}

impl<'g, T: BorrowMut<Transcript>> ConstraintSystem for Prover<'g, T> {
    fn transcript(&mut self) -> &mut Transcript {
        self.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.secrets.a_L.len());
        let r_var = Variable::MultiplierRight(self.secrets.a_R.len());
        let o_var = Variable::MultiplierOutput(self.secrets.a_O.len());
        // ... and assign them
        self.secrets.a_L.push(l);
        self.secrets.a_R.push(r);
        self.secrets.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::ONE));
        right.terms.push((r_var, -Scalar::ONE));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        let scalar = assignment.ok_or(R1CSError::MissingAssignment)?;

        match self.pending_multiplier {
            None => {
                let i = self.secrets.a_L.len();
                self.pending_multiplier = Some(i);
                self.secrets.a_L.push(scalar);
                self.secrets.a_R.push(Scalar::ZERO);
                self.secrets.a_O.push(Scalar::ZERO);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                self.secrets.a_R[i] = scalar;
                self.secrets.a_O[i] = self.secrets.a_L[i] * self.secrets.a_R[i];
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let (l, r) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.secrets.a_L.len());
        let r_var = Variable::MultiplierRight(self.secrets.a_R.len());
        let o_var = Variable::MultiplierOutput(self.secrets.a_O.len());
        // ... and assign them
        self.secrets.a_L.push(l);
        self.secrets.a_R.push(r);
        self.secrets.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn eval(&self, lc: &LinearCombination) -> Option<Scalar> {
        Some(self.eval(lc))
    }

    fn metrics(&self) -> Metrics {
        Metrics {
            multipliers: self.secrets.a_L.len(),
            constraints: self.constraints.len() + self.deferred_constraints.len(),
            phase_one_constraints: self.constraints.len(),
            phase_two_constraints: self.deferred_constraints.len(),
        }
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(&lc);
    }
}

impl<'g, T: BorrowMut<Transcript>> RandomizableConstraintSystem for Prover<'g, T> {
    type RandomizedCS = RandomizingProver<'g, T>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'g, T: BorrowMut<Transcript>> ConstraintSystem for RandomizingProver<'g, T> {
    fn transcript(&mut self) -> &mut Transcript {
        self.prover.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.prover.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.prover.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.prover.allocate_multiplier(input_assignments)
    }

    fn eval(&self, lc: &LinearCombination) -> Option<Scalar> {
        Some(self.prover.eval(lc))
    }

    fn metrics(&self) -> Metrics {
        self.prover.metrics()
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.prover.constrain(lc)
    }
}

impl<'g, T: BorrowMut<Transcript>> RandomizedConstraintSystem for RandomizingProver<'g, T> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.prover.transcript.borrow_mut().challenge_scalar(label)
    }
}

impl<'g, T: BorrowMut<Transcript>> Prover<'g, T> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(pc_gens: &'g PedersenGens, mut transcript: T) -> Self {
        transcript.borrow_mut().r1cs_domain_sep();

        Prover {
            pc_gens,
            transcript,
            secrets: Secrets {
                v: Vec::new(),
                v_blinding: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
            },
            constraints: ConstraintStore::default(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitment to the external variable for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, v: Scalar, v_blinding: Scalar) -> (CompressedRistretto, Variable) {
        let i = self.secrets.v.len();
        self.secrets.v.push(v);
        self.secrets.v_blinding.push(v_blinding);

        // Add the commitment to the transcript.
        let V = self.pc_gens.commit(v, v_blinding).compress();
        self.transcript.borrow_mut().append_point(b"V", &V);

        (V, Variable::Committed(i))
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(&mut self, z: &Scalar) -> Flattened {
        let (n, m) = (self.secrets.a_L.len(), self.secrets.v.len());
        self.constraints.flatten(z, n, m)
    }

    /// Returns the secret value of the linear combination.
    pub fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                coeff
                    * match var {
                        Variable::MultiplierLeft(i) => self.secrets.a_L[*i],
                        Variable::MultiplierRight(i) => self.secrets.a_R[*i],
                        Variable::MultiplierOutput(i) => self.secrets.a_O[*i],
                        Variable::Committed(i) => self.secrets.v[*i],
                        Variable::One() => Scalar::ONE,
                    }
            })
            .sum()
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.len() == 0 {
            self.transcript.borrow_mut().r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.borrow_mut().r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = mem::replace(&mut self.deferred_constraints, Vec::new());
            let mut wrapped_self = RandomizingProver { prover: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.prover)
        }
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(self, bp_gens: &BulletproofGens) -> Result<R1CSProof, R1CSError> {
        self.prove_and_return_transcript(bp_gens)
            .map(|(proof, _transcript)| proof)
    }

    /// Consume this `ConstraintSystem` to produce a proof. Returns the proof and the transcript passed in `Prover::new`.
    pub fn prove_and_return_transcript(
        self,
        bp_gens: &BulletproofGens,
    ) -> Result<(R1CSProof, T), R1CSError> {
        self.prove_with_rng_and_return_transcript(bp_gens, &mut rand::thread_rng())
    }

    /// As [`Prover::prove`], with the external randomness mixed into the transcript RNG
    /// taken from `rng` instead of `thread_rng()`. A fixed `rng` makes the proof
    /// deterministic, which is useful for test vectors; use a cryptographic RNG otherwise.
    pub fn prove_with_rng<R: RngCore + CryptoRng>(
        self,
        bp_gens: &BulletproofGens,
        rng: &mut R,
    ) -> Result<R1CSProof, R1CSError> {
        self.prove_with_rng_and_return_transcript(bp_gens, rng)
            .map(|(proof, _transcript)| proof)
    }

    fn prove_with_rng_and_return_transcript<R: RngCore + CryptoRng>(
        mut self,
        bp_gens: &BulletproofGens,
        external_rng: &mut R,
    ) -> Result<(R1CSProof, T), R1CSError> {
        use std::iter;

        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript
            .borrow_mut()
            .append_u64(b"m", self.secrets.v.len() as u64);

        // Create a `TranscriptRng` from the high-level witness data
        //
        // The prover wants to rekey the RNG with its witness data.
        //
        // This consists of the high level witness data (the v's and
        // v_blinding's), as well as the low-level witness data (a_L,
        // a_R, a_O).  Since the low-level data should (hopefully) be
        // determined by the high-level data, it doesn't give any
        // extra entropy for reseeding the RNG.
        //
        // Since the v_blindings should be random scalars (in order to
        // protect the v's in the commitments), we don't gain much by
        // committing the v's as well as the v_blinding's.
        let mut rng = {
            let mut builder = self.transcript.borrow_mut().build_rng();

            // Commit the blinding factors for the input wires
            for v_b in &self.secrets.v_blinding {
                builder = builder.rekey_with_witness_bytes(b"v_blinding", v_b.as_bytes());
            }

            builder.finalize(external_rng)
        };

        // Commit to the first-phase low-level witness variables.
        let n1 = self.secrets.a_L.len();

        if bp_gens.gens_capacity < n1 {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        let i_blinding1 = Scalar::random(&mut rng);
        let o_blinding1 = Scalar::random(&mut rng);
        let s_blinding1 = Scalar::random(&mut rng);

        let mut s_L1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I1 = util::chunked_msm(
            iter::once(&i_blinding1)
                .chain(self.secrets.a_L.iter())
                .chain(self.secrets.a_R.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
            util::MSM_CHUNK_CT,
            false,
        )
        .compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O1 = util::chunked_msm(
            iter::once(&o_blinding1).chain(self.secrets.a_O.iter()),
            iter::once(&self.pc_gens.B_blinding).chain(gens.G(n1)),
            util::MSM_CHUNK_CT,
            false,
        )
        .compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S1 = util::chunked_msm(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
            util::MSM_CHUNK_CT,
            false,
        )
        .compress();

        let transcript = self.transcript.borrow_mut();
        transcript.append_point(b"A_I1", &A_I1);
        transcript.append_point(b"A_O1", &A_O1);
        transcript.append_point(b"S1", &S1);

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        // Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.secrets.a_L.len();
        let n2 = n - n1;
        let padded_n = self.secrets.a_L.len().next_power_of_two();
        let pad = padded_n - n;

        if bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // Commit to the second-phase low-level witness variables

        let has_2nd_phase_commitments = n2 > 0;

        let (i_blinding2, o_blinding2, s_blinding2) = if has_2nd_phase_commitments {
            (
                Scalar::random(&mut rng),
                Scalar::random(&mut rng),
                Scalar::random(&mut rng),
            )
        } else {
            (Scalar::ZERO, Scalar::ZERO, Scalar::ZERO)
        };

        let mut s_L2: Vec<Scalar> = (0..n2).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R2: Vec<Scalar> = (0..n2).map(|_| Scalar::random(&mut rng)).collect();

        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            (
                // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                util::chunked_msm(
                    iter::once(&i_blinding2)
                        .chain(self.secrets.a_L.iter().skip(n1))
                        .chain(self.secrets.a_R.iter().skip(n1)),
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1)),
                    util::MSM_CHUNK_CT,
                    false,
                )
                .compress(),
                // A_O = <a_O, G> + o_blinding * B_blinding
                util::chunked_msm(
                    iter::once(&o_blinding2).chain(self.secrets.a_O.iter().skip(n1)),
                    iter::once(&self.pc_gens.B_blinding).chain(gens.G(n).skip(n1)),
                    util::MSM_CHUNK_CT,
                    false,
                )
                .compress(),
                // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                util::chunked_msm(
                    iter::once(&s_blinding2)
                        .chain(s_L2.iter())
                        .chain(s_R2.iter()),
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1)),
                    util::MSM_CHUNK_CT,
                    false,
                )
                .compress(),
            )
        } else {
            // Since we are using zero blinding factors and
            // there are no variables to commit,
            // the commitments _must_ be identity points,
            // so we can hardcode them saving 3 mults+compressions.
            (
                CompressedRistretto::identity(),
                CompressedRistretto::identity(),
                CompressedRistretto::identity(),
            )
        };

        let transcript = self.transcript.borrow_mut();
        transcript.append_point(b"A_I2", &A_I2);
        transcript.append_point(b"A_O2", &A_O2);
        transcript.append_point(b"S2", &S2);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        // t(X) = <l(X), r(X)>, accumulated per index without materialising the vector
        // polynomials (l_0 = r_2 = 0):
        //   l_1 = a_L + y^-i w_R,  l_2 = a_O,  l_3 = s_L,
        //   r_0 = w_O - y^i,  r_1 = y^i a_R + w_L,  r_3 = y^i s_R.
        let y_inv = y.invert();
        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();
        let s_L = |i: usize| if i < n1 { s_L1[i] } else { s_L2[i - n1] };
        let s_R = |i: usize| if i < n1 { s_R1[i] } else { s_R2[i - n1] };
        let secrets = &self.secrets;
        let coeffs = |i: usize, exp_y: Scalar| {
            let a = secrets;
            let l = (a.a_L[i] + exp_y_inv[i] * wR[i], a.a_O[i], s_L(i));
            let r = (wO[i] - exp_y, exp_y * a.a_R[i] + wL[i], exp_y * s_R(i));
            (l, r)
        };
        let mut t_poly = util::Poly6 {
            t1: Scalar::ZERO,
            t2: Scalar::ZERO,
            t3: Scalar::ZERO,
            t4: Scalar::ZERO,
            t5: Scalar::ZERO,
            t6: Scalar::ZERO,
        };
        let mut exp_y = Scalar::ONE; // y^i
        for i in 0..n {
            let ((l1, l2, l3), (r0, r1, r3)) = coeffs(i, exp_y);
            t_poly.t1 += l1 * r0;
            t_poly.t2 += l1 * r1 + l2 * r0;
            t_poly.t3 += l2 * r1 + l3 * r0;
            t_poly.t4 += l1 * r3 + l3 * r1;
            t_poly.t5 += l2 * r3;
            t_poly.t6 += l3 * r3;
            exp_y *= y;
        }

        let t_1_blinding = Scalar::random(&mut rng);
        let t_3_blinding = Scalar::random(&mut rng);
        let t_4_blinding = Scalar::random(&mut rng);
        let t_5_blinding = Scalar::random(&mut rng);
        let t_6_blinding = Scalar::random(&mut rng);

        let T_1 = self.pc_gens.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = self.pc_gens.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = self.pc_gens.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = self.pc_gens.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = self.pc_gens.commit(t_poly.t6, t_6_blinding).compress();

        let transcript = self.transcript.borrow_mut();
        transcript.append_point(b"T_1", &T_1);
        transcript.append_point(b"T_3", &T_3);
        transcript.append_point(b"T_4", &T_4);
        transcript.append_point(b"T_5", &T_5);
        transcript.append_point(b"T_6", &T_6);

        let u = transcript.challenge_scalar(b"u");
        let x = transcript.challenge_scalar(b"x");

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = wV
            .iter()
            .zip(self.secrets.v_blinding.iter())
            .map(|(c, v_blinding)| c * v_blinding)
            .sum();

        let t_blinding_poly = util::Poly6 {
            t1: t_1_blinding,
            t2: t_2_blinding,
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let mut l_vec = Vec::with_capacity(padded_n);
        let mut r_vec = Vec::with_capacity(padded_n);
        let mut exp_y = Scalar::ONE;
        for i in 0..n {
            let ((l1, l2, l3), (r0, r1, r3)) = coeffs(i, exp_y);
            l_vec.push(x * (l1 + x * (l2 + x * l3)));
            r_vec.push(r0 + x * (r1 + x * x * r3));
            exp_y *= y;
        }
        drop((wL, wR, wO));
        // The witness vectors are not needed by the inner-product argument: zero and free
        // them now rather than at the end, to lower the peak memory.
        for e in self
            .secrets
            .a_L
            .iter_mut()
            .chain(self.secrets.a_R.iter_mut())
            .chain(self.secrets.a_O.iter_mut())
            .chain(s_L1.iter_mut())
            .chain(s_L2.iter_mut())
            .chain(s_R1.iter_mut())
            .chain(s_R2.iter_mut())
        {
            e.clear();
        }
        for v in [&mut self.secrets.a_L, &mut self.secrets.a_R, &mut self.secrets.a_O, &mut s_L1, &mut s_L2, &mut s_R1, &mut s_R2] {
            *v = Vec::new();
        }
        // XXX this should refer to the notes to explain why this is correct
        for _ in n..padded_n {
            l_vec.push(Scalar::ZERO);
            r_vec.push(-exp_y);
            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let i_blinding = i_blinding1 + u * i_blinding2;
        let o_blinding = o_blinding1 + u * o_blinding2;
        let s_blinding = s_blinding1 + u * s_blinding2;

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        transcript.append_scalar(b"t_x", &t_x);
        transcript.append_scalar(b"t_x_blinding", &t_x_blinding);
        transcript.append_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let G_factors = iter::repeat(Scalar::ONE)
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad))
            .collect::<Vec<_>>();
        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y, u_or_1)| y * u_or_1)
            .collect::<Vec<_>>();

        let (G_gens, H_gens) = gens.G_H_slices(padded_n);
        let ipp_proof = InnerProductProof::create_from_slices(
            transcript, &Q, &G_factors, &H_factors, G_gens, H_gens, l_vec, r_vec,
        );

        // We do not yet have a ClearOnDrop wrapper for Vec<Scalar>.
        // When PR 202 [1] is merged, we can simply wrap s_L and s_R at the point of creation.
        // [1] https://github.com/dalek-cryptography/curve25519-dalek/pull/202
        for scalar in s_L1
            .iter_mut()
            .chain(s_L2.iter_mut())
            .chain(s_R1.iter_mut())
            .chain(s_R2.iter_mut())
        {
            scalar.clear();
        }
        let proof = R1CSProof {
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
        };
        Ok((proof, self.transcript))
    }
}

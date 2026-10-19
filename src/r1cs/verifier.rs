#![allow(non_snake_case)]

use core::borrow::BorrowMut;
use core::mem;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use super::{
    ConstraintSystem, LinearCombination, R1CSProof, RandomizableConstraintSystem,
    RandomizedConstraintSystem, Variable,
};

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::Metrics;
use crate::transcript::TranscriptProtocol;
use super::proof::ProofKind;
#[cfg(feature = "bppp")]
use super::proof::{BpppProof, BuilderProof};
use super::builder::{self, Builder, CircuitBuilder, Cost, Counts, Reciprocal, TableId};
use super::compact::{ConstraintStore, Flattened};

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<T: BorrowMut<Transcript>> {
    transcript: T,
    constraints: ConstraintStore,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<CompressedRistretto>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingVerifier<T>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,

    /// The proof system used by `verify`.
    backend: super::Backend,

    /// The circuit builder's record (spec §7).
    builder: Builder,

    /// First multiplier of the witness pairs (BP lowering, spec §7.5).
    witness_base: usize,
}

/// Verifier in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingVerifier<T: BorrowMut<Transcript>> {
    verifier: Verifier<T>,
}

impl<T: BorrowMut<Transcript>> ConstraintSystem for Verifier<T> {
    fn transcript(&mut self) -> &mut Transcript {
        self.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::ONE));
        right.terms.push((r_var, -Scalar::ONE));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        match self.pending_multiplier {
            None => {
                let i = self.num_vars;
                self.num_vars += 1;
                self.pending_multiplier = Some(i);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        _: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn eval(&self, _: &LinearCombination) -> Option<Scalar> {
        None
    }

    fn metrics(&self) -> Metrics {
        Metrics {
            multipliers: self.num_vars,
            constraints: self.constraints.len() + self.deferred_constraints.len(),
            phase_one_constraints: self.constraints.len(),
            phase_two_constraints: self.deferred_constraints.len(),
        }
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(&lc);
    }
}

impl<T: BorrowMut<Transcript>> CircuitBuilder for Verifier<T> {
    fn witness(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        Ok(self.builder.witness())
    }

    fn product(&mut self, l: LinearCombination, r: LinearCombination, out: LinearCombination) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.product(l, r, out, c)
    }

    fn table(&mut self, rows: Vec<Vec<u64>>) -> Result<TableId, R1CSError> {
        self.builder.table(rows)
    }

    fn lookup(&mut self, t: TableId, tuple: &[LinearCombination]) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.lookup(t, tuple, c)
    }

    fn lookup_value(&mut self, t: TableId, v: Option<u64>) -> Result<Variable, R1CSError> {
        self.builder.check_value_table(t)?;
        let x = CircuitBuilder::witness(self, v.map(Scalar::from))?;
        self.lookup(t, &[x.into()])?;
        Ok(x)
    }

    fn finish_reciprocal(&mut self, r: Reciprocal) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.finish_reciprocal(r, c)
    }

    fn cost(&self) -> Cost {
        self.builder.cost(self.num_vars, self.V.len())
    }
}

impl<T: BorrowMut<Transcript>> RandomizableConstraintSystem for Verifier<T> {
    type RandomizedCS = RandomizingVerifier<T>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<T: BorrowMut<Transcript>> ConstraintSystem for RandomizingVerifier<T> {
    fn transcript(&mut self) -> &mut Transcript {
        self.verifier.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.verifier.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.verifier.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.verifier.allocate_multiplier(input_assignments)
    }

    fn eval(&self, _: &LinearCombination) -> Option<Scalar> {
        None    
    }

    fn metrics(&self) -> Metrics {
        self.verifier.metrics()
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.verifier.constrain(lc)
    }
}

impl<T: BorrowMut<Transcript>> RandomizedConstraintSystem for RandomizingVerifier<T> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.verifier
            .transcript
            .borrow_mut()
            .challenge_scalar(label)
    }
}

impl<T: BorrowMut<Transcript>> Verifier<T> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(mut transcript: T) -> Self {
        transcript.borrow_mut().r1cs_domain_sep();

        Verifier {
            transcript,
            num_vars: 0,
            V: Vec::new(),
            constraints: ConstraintStore::new(true),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
            backend: super::Backend::default(),
            builder: Builder::default(),
            witness_base: 0,
        }
    }

    /// Choose the proof system for [`Verifier::verify`] (default: [`Backend::Bp`](super::Backend));
    /// a proof of the other backend is rejected. See [`Prover::set_backend`](super::Prover::set_backend)
    /// for what changes with `Backend::Bppp`.
    pub fn set_backend(&mut self, backend: super::Backend) {
        self.backend = backend;
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: CompressedRistretto) -> Variable {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript.borrow_mut().append_point(b"V", &commitment);

        Variable::Committed(i)
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(&mut self, z: &Scalar) -> Flattened {
        let (n, m) = (self.num_vars, self.V.len());
        self.constraints.flatten(z, n, m, self.witness_base)
    }

    fn counts(&self) -> Counts {
        Counts { n: self.num_vars, k: self.V.len() }
    }

    /// The BP lowering of the builder's record (spec §7.4, §7.5), as the prover's.
    fn lower_builder_bp(&mut self) -> Result<(), R1CSError> {
        if !self.builder.active {
            return Ok(());
        }
        self.builder.finalize(None)?;
        self.witness_base = self.num_vars;
        self.num_vars += (self.builder.n_w + 1) / 2;
        for (l, r, out) in core::mem::take(&mut self.builder.products) {
            let (_, _, o) = self.multiply(l, r);
            self.constrain(o - out);
        }
        for arg in core::mem::take(&mut self.builder.args) {
            self.specify_randomized_constraints(move |cs| builder::logup(cs, arg))?;
        }
        Ok(())
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
            let mut wrapped_self = RandomizingVerifier { verifier: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.verifier)
        }
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    pub fn verify(
        self,
        proof: &R1CSProof,
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
    ) -> Result<(), R1CSError> {
        self.verify_and_return_transcript(proof, pc_gens, bp_gens)
            .map(|_| ())
    }
    /// Finalize the builder's record and lower it (spec §7.4, §7.6).
    #[cfg(feature = "bppp")]
    pub(crate) fn lower_builder_bppp(&mut self) -> Result<crate::bppp::ReciprocalCircuit, R1CSError> {
        self.builder.finalize(None)?;
        let rec = super::backend::Record {
            n: self.num_vars,
            k: self.V.len(),
            n_w: self.builder.n_w,
            products: &self.builder.products,
            args: &self.builder.args,
        };
        Ok(super::backend::builder_circuit(&self.constraints, &rec, None)?.0)
    }

    /// The BP++ backend for a builder circuit (spec §7.6, §7.7): lower the record and verify.
    #[cfg(feature = "bppp")]
    fn verify_builder(mut self, p: &BuilderProof, pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<T, R1CSError> {
        use crate::bppp::{reciprocal, BpppGens, BpppTranscript};
        if !self.deferred_constraints.is_empty() {
            return Err(R1CSError::GadgetError {
                description: "randomized constraints need the BP backend".into(),
            });
        }
        let c = self.lower_builder_bppp()?;
        if p.n_mm != c.n_p + c.n_m || p.n_lin != c.n_lin {
            return Err(R1CSError::VerificationError);
        }
        let gens = BpppGens::new(pc_gens, bp_gens, c.n_lin, p.n_mm).map_err(|_| R1CSError::InvalidGeneratorsLength)?;
        let transcript = self.transcript.borrow_mut();
        BpppTranscript::domain_sep(transcript, b"bppp-builder v1");
        reciprocal::verify(&p.proof, &c, &gens, &self.V, transcript).map_err(|_| R1CSError::VerificationError)?;
        Ok(self.transcript)
    }

    /// The BP++ backend (spec §6): rebuild the translated circuit and verify its proof.
    #[cfg(feature = "bppp")]
    fn verify_bppp(mut self, p: &BpppProof, pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<T, R1CSError> {
        use crate::bppp::{BpppGens, BpppTranscript};
        if !self.deferred_constraints.is_empty() {
            return Err(R1CSError::GadgetError {
                description: "randomized constraints need the BP backend".into(),
            });
        }
        let (n, k) = (self.num_vars, self.V.len());
        if p.n_m != super::backend::n_m(n) || p.k != k {
            return Err(R1CSError::VerificationError);
        }
        let c = super::backend::circuit(&self.constraints, n, k, super::backend::Constants::Stored)?;
        let gens = BpppGens::new(pc_gens, bp_gens, k, p.n_m).map_err(|_| R1CSError::InvalidGeneratorsLength)?;
        let transcript = self.transcript.borrow_mut();
        BpppTranscript::domain_sep(transcript, b"bppp-r1cs v1");
        p.proof.verify(&c, &gens, &self.V, transcript).map_err(|_| R1CSError::VerificationError)?;
        Ok(self.transcript)
    }

    /// Same as `verify`, but also returns the transcript back to the user.
    pub fn verify_and_return_transcript(
        mut self,
        proof: &R1CSProof,
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
    ) -> Result<T, R1CSError> {
        #[cfg(feature = "bppp")]
        {
            match &proof.0 {
                ProofKind::Bppp(_) | ProofKind::Builder(_) if self.backend != super::Backend::Bppp => {
                    return Err(R1CSError::VerificationError)
                }
                ProofKind::Bppp(p) if !self.builder.active => return self.verify_bppp(p, pc_gens, bp_gens),
                ProofKind::Builder(p) if self.builder.active => return self.verify_builder(p, pc_gens, bp_gens),
                ProofKind::Bppp(_) | ProofKind::Builder(_) => return Err(R1CSError::VerificationError),
                _ => {}
            }
            if self.backend == super::Backend::Bppp {
                return Err(R1CSError::VerificationError);
            }
        }
        let proof = match &proof.0 {
            ProofKind::Bp(p) => p,
            #[allow(unreachable_patterns)]
            _ => return Err(R1CSError::VerificationError),
        };
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        let transcript = self.transcript.borrow_mut();
        transcript.append_u64(b"m", self.V.len() as u64);

        self.lower_builder_bp()?;
        let transcript = self.transcript.borrow_mut();
        let n1 = self.num_vars;
        transcript.validate_and_append_point(b"A_I1", &proof.A_I1)?;
        transcript.validate_and_append_point(b"A_O1", &proof.A_O1)?;
        transcript.validate_and_append_point(b"S1", &proof.S1)?;

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        let transcript = self.transcript.borrow_mut();

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.num_vars;
        let padded_n = self.num_vars.next_power_of_two();

        use crate::util;
        use std::iter;

        if bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }
        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        // These points are the identity in the 1-phase unrandomized case.
        transcript.append_point(b"A_I2", &proof.A_I2);
        transcript.append_point(b"A_O2", &proof.A_O2);
        transcript.append_point(b"S2", &proof.S2);

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        if !self.constraints.vars_exist(self.num_vars, self.V.len(), self.builder.n_w) {
            return Err(builder::gadget_error("a constraint uses a variable outside the constraint system"));
        }

        transcript.validate_and_append_point(b"T_1", &proof.T_1)?;
        transcript.validate_and_append_point(b"T_3", &proof.T_3)?;
        transcript.validate_and_append_point(b"T_4", &proof.T_4)?;
        transcript.validate_and_append_point(b"T_5", &proof.T_5)?;
        transcript.validate_and_append_point(b"T_6", &proof.T_6)?;

        let u = transcript.challenge_scalar(b"u");
        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &proof.t_x);
        transcript.append_scalar(b"t_x_blinding", &proof.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &proof.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript.borrow_mut())
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.invert();
        let y_inv_vec = util::powers(y_inv, padded_n);
        let yneg_wR = util::map_index(padded_n, |i| if i < n { wR[i] * y_inv_vec[i] } else { Scalar::ZERO });
        drop(wR);

        let delta = util::inner_product_par(&yneg_wR[0..n], &wL);

        // Scalars of the G and H generators, computed per index (in parallel with `parallel`).
        let u_or_1 = |i: usize| if i < n1 { Scalar::ONE } else { u };
        let g_scalars = util::map_index(padded_n, |i| u_or_1(i) * (x * yneg_wR[i] - a * s[i]));
        let h_scalars = util::map_index(padded_n, |i| {
            let (wLi, wOi) = if i < n { (wL[i], wO[i]) } else { (Scalar::ZERO, Scalar::ZERO) };
            u_or_1(i) * (y_inv_vec[i] * (x * wLi + wOi - b * s[padded_n - 1 - i]) - Scalar::ONE)
        });
        drop((wL, wO, yneg_wR, y_inv_vec, s));

        use rand::thread_rng;
        let mut rng = self
            .transcript
            .borrow_mut()
            .build_rng()
            .finalize(&mut thread_rng());
        let r = Scalar::random(&mut rng);

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let decompress = |points: &mut dyn Iterator<Item = &CompressedRistretto>| {
            points
                .map(|p| p.decompress())
                .collect::<Option<Vec<RistrettoPoint>>>()
                .ok_or(R1CSError::VerificationError)
        };
        let head = decompress(
            &mut [proof.A_I1, proof.A_O1, proof.S1, proof.A_I2, proof.A_O2, proof.S2]
                .iter()
                .chain(self.V.iter())
                .chain(T_points.iter()),
        )?;
        let L_points = decompress(&mut proof.ipp_proof.L_vec.iter())?;
        let R_points = decompress(&mut proof.ipp_proof.R_vec.iter())?;

        // The final check is one multiscalar multiplication: the few proof points directly,
        // the generator parts over slices without copying (in parallel with `parallel`).
        let (G_gens, H_gens) = gens.G_H_slices(padded_n);
        let small = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(x) // A_I1
                .chain(iter::once(xx)) // A_O1
                .chain(iter::once(xxx)) // S1
                .chain(iter::once(u * x)) // A_I2
                .chain(iter::once(u * xx)) // A_O2
                .chain(iter::once(u * xxx)) // S2
                .chain(wV.iter().map(|wVi| wVi * rxx)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * (wc + delta) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()), // ipp_proof.R_vec
            head.iter()
                .chain(iter::once(&pc_gens.B))
                .chain(iter::once(&pc_gens.B_blinding))
                .chain(L_points.iter())
                .chain(R_points.iter()),
        );
        let mega_check = small
            + util::vartime_msm_slices(&g_scalars, G_gens, util::MSM_CHUNK_VT)
            + util::vartime_msm_slices(&h_scalars, H_gens, util::MSM_CHUNK_VT);
        use curve25519_dalek::traits::IsIdentity;

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(self.transcript)
    }
}

#![allow(non_snake_case)]

use core::mem;
use ff::Field as _;
use group::Group;

use super::{
    ConstraintSystem, LinearCombination, R1CSProof, RandomizableConstraintSystem,
    RandomizedConstraintSystem, Var, Variable,
};

use crate::curve::Curve;
use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::transcript::{TranscriptBackend, TranscriptProtocol, TranscriptRef};
use super::proof::ProofKind;
use super::proof::BpppProof;
use super::builder::{self, Builder, Cost, Counts, Reciprocal, TableId, Wire};
use super::compact::{ConstraintStore, Flattened, Input};

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<T: TranscriptRef, C: Curve> {
    transcript: T,
    constraints: ConstraintStore<C::Scalar>,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `Verifier` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<C::Compressed>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingVerifier<T, C>) -> Result<(), R1CSError>>>,


    /// The proof system used by `verify`.
    backend: super::Backend,

    /// The circuit builder's record (spec §7).
    builder: Builder<C::Scalar>,

    /// The BP multiplier input of every witness (BP lowering, spec §7.5).
    witness_inputs: Vec<Input>,
}

/// Verifier in the randomizing phase (the second phase of the BP backend).
pub(crate) struct RandomizingVerifier<T: TranscriptRef, C: Curve> {
    verifier: Verifier<T, C>,
}

impl<T: TranscriptRef, C: Curve> ConstraintSystem<C::Scalar> for Verifier<T, C> {
    fn transcript(&mut self) -> &mut dyn TranscriptBackend {
        self.transcript.backend()
    }

    fn witness(&mut self, _: Option<C::Scalar>) -> Result<Variable, R1CSError> {
        Ok(self.builder.witness())
    }

    fn multiply(&mut self, left: LinearCombination<C::Scalar>, right: LinearCombination<C::Scalar>) -> Result<Variable, R1CSError> {
        let i = self.num_vars;
        let fold = (self.builder.fold(&left, Wire::Left(i)), self.builder.fold(&right, Wire::Right(i)));
        Ok(self.multiplier(left, right, fold).2)
    }

    fn constrain_product(&mut self, l: LinearCombination<C::Scalar>, r: LinearCombination<C::Scalar>, out: LinearCombination<C::Scalar>) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.constrain_product(l, r, out, c)
    }

    fn constrain(&mut self, lc: LinearCombination<C::Scalar>) {
        self.constraints.push(&lc);
    }

    fn eval(&self, _: &LinearCombination<C::Scalar>) -> Option<C::Scalar> {
        None
    }

    fn table(&mut self, rows: Vec<Vec<u64>>) -> Result<TableId, R1CSError> {
        self.builder.table(rows)
    }

    fn lookup(&mut self, t: TableId, tuple: &[LinearCombination<C::Scalar>]) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.lookup(t, tuple, c)
    }

    fn lookup_value(&mut self, t: TableId, v: Option<u64>) -> Result<Variable, R1CSError> {
        self.builder.check_value_table(t)?;
        let x = self.witness(v.map(C::Scalar::from))?;
        self.lookup(t, &[x.into()])?;
        Ok(x)
    }

    fn reciprocal(&mut self, m: usize) -> Result<Reciprocal, R1CSError> {
        self.builder.reciprocal(m)
    }

    fn reciprocal_term(&mut self, r: Reciprocal, num: LinearCombination<C::Scalar>, tuple: &[LinearCombination<C::Scalar>]) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.reciprocal_term(r, num, tuple, c)
    }

    fn reciprocal_public(&mut self, r: Reciprocal, coeff: LinearCombination<C::Scalar>, row: &[u64]) -> Result<(), R1CSError> {
        let c = self.counts();
        self.builder.reciprocal_public(r, coeff, row, c)
    }

    fn cost(&self) -> Cost {
        self.builder.cost(self.num_vars, self.V.len())
    }
}

impl<T: TranscriptRef, C: Curve> RandomizableConstraintSystem<C::Scalar> for Verifier<T, C> {
    type RandomizedCS = RandomizingVerifier<T, C>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<T: TranscriptRef, C: Curve> RandomizedConstraintSystem<C::Scalar> for RandomizingVerifier<T, C> {
    fn multiply(&mut self, l: LinearCombination<C::Scalar>, r: LinearCombination<C::Scalar>) -> (Variable, Variable, Variable) {
        self.verifier.multiplier(l, r, (false, false))
    }

    fn allocate_multiplier(&mut self, _: Option<(C::Scalar, C::Scalar)>) -> Result<(Variable, Variable, Variable), R1CSError> {
        Ok(self.verifier.free_multiplier())
    }

    fn constrain(&mut self, lc: LinearCombination<C::Scalar>) {
        self.verifier.constraints.push(&lc);
    }

    fn eval(&self, _: &LinearCombination<C::Scalar>) -> Option<C::Scalar> {
        None
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> C::Scalar {
        self.verifier.transcript.backend().challenge_scalar(label)
    }
}

#[cfg(feature = "simplicity")]
impl<T: TranscriptRef<Backend = crate::simplicity::CompileTranscript>> Verifier<T, crate::curve::Secp256k1> {
    /// Compile the circuit (backend BP++, no randomized constraints) into a Simplicity program
    /// that verifies its proofs, bound to the spending transaction: the transcript must hold a
    /// [`SIGHASH_LABEL`](crate::simplicity::SIGHASH_LABEL) record where the prover's holds
    /// the transaction's hash (docs/simplicity-verifier.md).
    pub fn compile_to_simplicity(
        mut self,
        pc_gens: &PedersenGens<crate::curve::Secp256k1>,
        bp_gens: &BulletproofGens<crate::curve::Secp256k1>,
    ) -> Result<crate::simplicity::SimplicityVerifier, R1CSError> {
        if self.backend != super::Backend::Bppp {
            return Err(R1CSError::GadgetError { description: "a Simplicity verifier needs the BP++ backend".into() });
        }
        super::backend::refuse_randomized(self.deferred_constraints.len())?;
        let c = self.lower_builder_bppp()?;
        crate::simplicity::compile(&c, &self.V, self.transcript.backend_ref(), pc_gens, bp_gens)
    }
}

impl<T: TranscriptRef, C: Curve> Verifier<T, C> {
    /// A BP multiplier with `left = l`, `right = r`; returns `(left, right, out)`. An input
    /// that is a folded witness (`fold`) is the wire itself, without a linear constraint.
    fn multiplier(&mut self, mut l: LinearCombination<C::Scalar>, mut r: LinearCombination<C::Scalar>, fold: (bool, bool)) -> (Variable, Variable, Variable) {
        let (l_var, r_var, o_var) = self.free_multiplier();
        if !fold.0 {
            l.terms.push((l_var, -C::Scalar::ONE));
            self.constraints.push(&l);
        }
        if !fold.1 {
            r.terms.push((r_var, -C::Scalar::ONE));
            self.constraints.push(&r);
        }
        (l_var, r_var, o_var)
    }

    /// A BP multiplier with free inputs; returns `(left, right, out)`.
    fn free_multiplier(&mut self) -> (Variable, Variable, Variable) {
        let i = self.num_vars;
        self.num_vars += 1;
        (Variable(Var::MultiplierLeft(i)), Variable(Var::MultiplierRight(i)), Variable(Var::MultiplierOutput(i)))
    }

    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a proof transcript (`merlin::Transcript`, a
    /// `Sha256Transcript` or any [`TranscriptBackend`]) or a mutable borrow of one.  The
    /// `Verifier` holds onto the transcript until it consumes
    /// itself during [`Verifier::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `Verifier` before proving is complete.
    ///
    /// Commit the external variables with [`Verifier::commit`] before any challenge is
    /// drawn (the randomized constraints of the second phase), so that the challenges are
    /// bound to them.
    pub fn new(mut transcript: T) -> Self {
        transcript.backend().r1cs_domain_sep();
        transcript.backend().curve_domain_sep::<C>();

        Verifier {
            transcript,
            num_vars: 0,
            V: Vec::new(),
            constraints: ConstraintStore::new(true),
            deferred_constraints: Vec::new(),
            backend: super::Backend::default(),
            builder: Builder::default(),
            witness_inputs: Vec::new(),
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
    pub fn commit(&mut self, commitment: C::Compressed) -> Variable {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript.backend().append_point(b"V", &commitment);

        Variable(Var::Committed(i))
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
    /// This has the same logic as `Prover::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(&mut self, z: &C::Scalar) -> Flattened<C::Scalar> {
        let (n, m) = (self.num_vars, self.V.len());
        self.constraints.flatten(z, n, m, &self.witness_inputs)
    }

    fn counts(&self) -> Counts {
        Counts { n: self.num_vars, k: self.V.len() }
    }

    /// The BP lowering of the builder's record (spec §7.4, §7.5), as the prover's.
    fn lower_builder_bp(&mut self) -> Result<(), R1CSError> {
        // an empty record (a plain R1CS) adds nothing
        self.builder.finalize(None)?;
        let place = self.builder.placement();
        let witness_base = self.num_vars;
        self.num_vars += (place.n_free + 1) / 2;
        let product_base = self.num_vars;
        for ((l, r, out), fold) in core::mem::take(&mut self.builder.products).into_iter().zip(place.product_folded.iter().copied()) {
            let (_, _, o) = self.multiplier(l, r, fold);
            self.constraints.push(&(o - out));
        }
        self.witness_inputs = place.bp_inputs(witness_base, product_base);
        for arg in core::mem::take(&mut self.builder.args) {
            self.specify_randomized_constraints(move |cs| builder::logup(cs, arg))?;
        }
        Ok(())
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {

        if self.deferred_constraints.len() == 0 {
            self.transcript.backend().r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.backend().r1cs_2phase_domain_sep();
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

    /// Consume this `Verifier` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    pub fn verify(
        self,
        proof: &R1CSProof<C>,
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(), R1CSError> {
        self.verify_and_return_transcript(proof, pc_gens, bp_gens)
            .map(|_| ())
    }
    /// Finalize the builder's record and lower it (spec §7.4, §7.6).
    pub(crate) fn lower_builder_bppp(&mut self) -> Result<crate::bppp::ReciprocalCircuit<C::Scalar>, R1CSError> {
        self.builder.finalize(None)?;
        let place = self.builder.placement();
        let rec = super::backend::Record {
            n: self.num_vars,
            k: self.V.len(),
            n_w: self.builder.n_w,
            place: &place,
            products: &self.builder.products,
            args: &self.builder.args,
        };
        Ok(super::backend::builder_circuit(&self.constraints, &rec, None)?.0)
    }

    /// The BP++ backend (spec §6, §7.6): lower the constraint system (with the builder's record,
    /// empty for a plain R1CS) and verify.
    fn verify_bppp(mut self, p: &BpppProof<C>, pc_gens: &PedersenGens<C>, bp_gens: &BulletproofGens<C>) -> Result<T, R1CSError> {
        use crate::bppp::{reciprocal, BpppGens, BpppTranscript};
        super::backend::refuse_randomized(self.deferred_constraints.len())?;
        let c = self.lower_builder_bppp()?;
        if p.n_mm != c.n_p + c.n_m || p.n_lin != c.n_lin {
            return Err(R1CSError::VerificationError);
        }
        let gens = BpppGens::new(pc_gens, bp_gens, c.n_lin, p.n_mm).map_err(|_| R1CSError::InvalidGeneratorsLength)?;
        let transcript = self.transcript.backend();
        BpppTranscript::domain_sep(transcript, super::backend::BPPP_DOMAIN);
        reciprocal::verify(&p.proof, &c, &gens, &self.V, transcript).map_err(|_| R1CSError::VerificationError)?;
        Ok(self.transcript)
    }

    /// Same as `verify`, but also returns the transcript back to the user.
    pub fn verify_and_return_transcript(
        mut self,
        proof: &R1CSProof<C>,
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<T, R1CSError> {
        // a proof of the other backend is rejected
        let proof = match (self.backend, &proof.0) {
            (super::Backend::Bp, ProofKind::Bp(p)) => p,
            (super::Backend::Bppp, ProofKind::Bppp(p)) => return self.verify_bppp(p, pc_gens, bp_gens),
            #[allow(unreachable_patterns)]
            _ => return Err(R1CSError::VerificationError),
        };
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        let transcript = self.transcript.backend();
        transcript.append_u64(b"m", self.V.len() as u64);

        self.lower_builder_bp()?;
        let transcript = self.transcript.backend();
        let n1 = self.num_vars;
        transcript.validate_and_append_point(b"A_I1", &proof.A_I1)?;
        transcript.validate_and_append_point(b"A_O1", &proof.A_O1)?;
        transcript.validate_and_append_point(b"S1", &proof.S1)?;

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        let transcript = self.transcript.backend();

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

        let y: C::Scalar = transcript.challenge_scalar(b"y");
        let z: C::Scalar = transcript.challenge_scalar(b"z");
        if !self.constraints.vars_exist(self.num_vars, self.V.len(), self.builder.n_w) {
            return Err(builder::gadget_error("a constraint uses a variable outside the constraint system"));
        }

        transcript.validate_and_append_point(b"T_1", &proof.T_1)?;
        transcript.validate_and_append_point(b"T_3", &proof.T_3)?;
        transcript.validate_and_append_point(b"T_4", &proof.T_4)?;
        transcript.validate_and_append_point(b"T_5", &proof.T_5)?;
        transcript.validate_and_append_point(b"T_6", &proof.T_6)?;

        let u: C::Scalar = transcript.challenge_scalar(b"u");
        let x: C::Scalar = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &proof.t_x);
        transcript.append_scalar(b"t_x_blinding", &proof.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &proof.e_blinding);

        let w: C::Scalar = transcript.challenge_scalar(b"w");

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript.backend())
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = util::invert(y);
        let y_inv_vec = util::powers(y_inv, padded_n);
        let yneg_wR = util::map_index(padded_n, |i| if i < n { wR[i] * y_inv_vec[i] } else { C::Scalar::ZERO });
        drop(wR);

        let delta = util::inner_product_par(&yneg_wR[0..n], &wL);

        // Scalars of the G and H generators, computed per index (in parallel with `parallel`).
        let u_or_1 = |i: usize| if i < n1 { C::Scalar::ONE } else { u };
        let g_scalars = util::map_index(padded_n, |i| u_or_1(i) * (x * yneg_wR[i] - a * s[i]));
        let h_scalars = util::map_index(padded_n, |i| {
            let (wLi, wOi) = if i < n { (wL[i], wO[i]) } else { (C::Scalar::ZERO, C::Scalar::ZERO) };
            u_or_1(i) * (y_inv_vec[i] * (x * wLi + wOi - b * s[padded_n - 1 - i]) - C::Scalar::ONE)
        });
        drop((wL, wO, yneg_wR, y_inv_vec, s));

        use rand::thread_rng;
        let mut rng = self
            .transcript
            .backend()
            .build_rng()
            .finalize(&mut thread_rng());
        let r = C::Scalar::random(&mut rng);

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let decompress = |points: &mut dyn Iterator<Item = &C::Compressed>| {
            points
                .map(|p| C::decompress(p))
                .collect::<Option<Vec<C::Point>>>()
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
        let small_scalars: Vec<C::Scalar> = iter::once(x) // A_I1
                .chain(iter::once(xx)) // A_O1
                .chain(iter::once(xxx)) // S1
                .chain(iter::once(u * x)) // A_I2
                .chain(iter::once(u * xx)) // A_O2
                .chain(iter::once(u * xxx)) // S2
                .chain(wV.iter().map(|wVi| *wVi * rxx)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * (wc + delta) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()) // ipp_proof.R_vec
                .collect();
        let small_points: Vec<C::Point> = head
            .iter()
            .chain(iter::once(&pc_gens.B))
            .chain(iter::once(&pc_gens.B_blinding))
            .chain(L_points.iter())
            .chain(R_points.iter())
            .copied()
            .collect();
        let mega_check =
            C::msm_vt(&small_scalars, &small_points) + C::msm_vt(&g_scalars, G_gens) + C::msm_vt(&h_scalars, H_gens);

        if !bool::from(mega_check.is_identity()) {
            return Err(R1CSError::VerificationError);
        }

        Ok(self.transcript)
    }
}

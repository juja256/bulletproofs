//! Proving backends of the R1CS front end (spec §6).

/// The proof system that proves a constraint system. Chosen with
/// [`Prover::set_backend`](super::Prover::set_backend) and
/// [`Verifier::set_backend`](super::Verifier::set_backend); `prove` and `verify` keep their
/// signatures.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Backend {
    /// Bulletproofs (the upstream protocol).
    #[default]
    Bp,
    /// Bulletproofs++: the constraint system is translated into an arithmetic circuit
    /// (spec §6) and proven with the protocol of spec §3. Randomized constraints are not
    /// supported.
    #[cfg(feature = "bppp")]
    Bppp,
}

#[cfg(feature = "bppp")]
pub(super) use self::bppp_backend::*;

#[cfg(feature = "bppp")]
mod bppp_backend {
    use alloc::vec;
    use alloc::vec::Vec;

    use curve25519_dalek::scalar::Scalar;

    use super::super::compact::ConstraintStore;
    use super::super::Variable;
    use crate::bppp::{ArithmeticCircuit, CircuitProof, CircuitWitness, Slot, SparseMatrix};
    use crate::errors::R1CSError;

    /// Multiplications of the translated circuit for `n` multipliers (at least one).
    pub(crate) fn n_m(n: usize) -> usize {
        n.max(1)
    }

    /// Where the constants of the constraints come from.
    pub(crate) enum Constants<'a> {
        /// Stored in the constraint store (the verifier).
        Stored,
        /// `-sum c x` over the witness (the prover, whose store drops constants): equal to
        /// the stored constants exactly when the witness satisfies the linear constraints.
        FromWitness {
            a_l: &'a [Scalar],
            a_r: &'a [Scalar],
            a_o: &'a [Scalar],
            v: &'a [Scalar],
        },
    }

    /// The arithmetic circuit of an R1CS with `n` multipliers and `k` committed inputs
    /// (spec §6): `w_L = a_L`, `w_R = a_R`, `w_O = a_O || c`, `W_m` selects `a_O`, the first
    /// `k` linear rows copy the inputs (`v_j - c_j = 0`), then every constraint with its
    /// constant in `a_l`. A variable outside the constraint system is a `GadgetError`.
    pub(crate) fn circuit(store: &ConstraintStore, n: usize, k: usize, constants: Constants) -> Result<ArithmeticCircuit, R1CSError> {
        let n_m = n_m(n);
        let n_w = 3 * n_m + k;
        let copy = |j: usize| 3 * n_m + j;
        let mut w_l = SparseMatrix::new(n_w);
        let mut a_l = Vec::with_capacity(k + store.len());
        for j in 0..k {
            w_l.push_row(vec![(copy(j), -Scalar::ONE)]);
            a_l.push(Scalar::ZERO);
        }
        let unknown = || R1CSError::GadgetError { description: "a constraint uses a variable outside the constraint system".into() };
        for q in 0..store.len() {
            let mut constant = Scalar::ZERO;
            let mut terms = Vec::new();
            for (var, c) in store.row(q) {
                let col = match var {
                    Variable::MultiplierLeft(i) if i < n => i,
                    Variable::MultiplierRight(i) if i < n => n_m + i,
                    Variable::MultiplierOutput(i) if i < n => 2 * n_m + i,
                    Variable::Committed(j) if j < k => copy(j),
                    Variable::One() => {
                        constant += c;
                        continue;
                    }
                    _ => return Err(unknown()),
                };
                if let Constants::FromWitness { a_l, a_r, a_o, v } = &constants {
                    let x = match var {
                        Variable::MultiplierLeft(i) => a_l[i],
                        Variable::MultiplierRight(i) => a_r[i],
                        Variable::MultiplierOutput(i) => a_o[i],
                        Variable::Committed(j) => v[j],
                        Variable::One() => Scalar::ZERO,
                    };
                    constant -= c * x;
                }
                terms.push((col, c));
            }
            w_l.push_row(terms);
            a_l.push(constant);
        }
        let mut w_m = SparseMatrix::new(n_w);
        for i in 0..n_m {
            w_m.push_row(vec![(2 * n_m + i, Scalar::ONE)]);
        }
        Ok(ArithmeticCircuit {
            n_m,
            n_o: n_m + k,
            n_v: 1,
            n_lin: k,
            k,
            w_l,
            a_l,
            w_m,
            a_m: vec![Scalar::ZERO; n_m],
            f_l: k > 0,
            f_m: false,
            partition: (0..n_m).map(|i| (Slot::NormO, i)).chain((0..k).map(|j| (Slot::LinO, j))).collect(),
        })
    }

    /// The witness of the translated circuit.
    pub(crate) fn witness(
        a_l: &[Scalar],
        a_r: &[Scalar],
        a_o: &[Scalar],
        v: &[Scalar],
        v_blinding: &[Scalar],
    ) -> CircuitWitness {
        let n_m = n_m(a_l.len());
        let pad = |x: &[Scalar]| -> Vec<Scalar> {
            let mut out = x.to_vec();
            out.resize(n_m, Scalar::ZERO);
            out
        };
        CircuitWitness {
            w_l: pad(a_l),
            w_r: pad(a_r),
            w_o: pad(a_o).into_iter().chain(v.iter().copied()).collect(),
            v: v.iter().map(|x| vec![*x]).collect(),
            s: v_blinding.to_vec(),
        }
    }

    /// Parse the circuit proof of a translated R1CS with these dimensions.
    pub(crate) fn proof_from_bytes(bytes: &[u8], n_m: usize, k: usize) -> Result<CircuitProof, R1CSError> {
        if n_m == 0 {
            return Err(R1CSError::FormatError);
        }
        let shape = ArithmeticCircuit {
            n_m,
            n_o: 0,
            n_v: 1,
            n_lin: k,
            k,
            w_l: SparseMatrix::new(0),
            a_l: vec![],
            w_m: SparseMatrix::new(0),
            a_m: vec![],
            f_l: true,
            f_m: false,
            partition: vec![],
        };
        CircuitProof::from_bytes(bytes, &shape).map_err(|_| R1CSError::FormatError)
    }
}

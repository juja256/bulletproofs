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
    /// Bulletproofs++: the constraint system (with its builder operations, if any) is lowered
    /// to a reciprocal form circuit (spec §6, §7.6) and proven with the protocol of spec §4.
    /// Randomized constraints are not supported.
    #[cfg(feature = "bppp")]
    Bppp,
}

#[cfg(feature = "bppp")]
pub(super) use self::bppp_backend::*;

/// The domain separator of the R1CS front end on BP++ (spec §6.2).
#[cfg(feature = "bppp")]
pub(super) const BPPP_DOMAIN: &[u8] = b"bppp-r1cs v2";

/// BP++ has no second phase of arbitrary randomized constraints (spec §6.1): a gadget that
/// specified any gets a `GadgetError` (lookups and permutations go through `CircuitBuilder`).
#[cfg(feature = "bppp")]
pub(super) fn refuse_randomized(n_deferred: usize) -> Result<(), crate::errors::R1CSError> {
    if n_deferred == 0 {
        Ok(())
    } else {
        Err(crate::errors::R1CSError::GadgetError { description: "randomized constraints need the BP backend".into() })
    }
}

#[cfg(feature = "bppp")]
mod bppp_backend {
    use alloc::vec;
    use alloc::vec::Vec;

    use curve25519_dalek::scalar::Scalar;

    use super::super::builder::{gadget_error, needs_early_copy, Argument};
    use super::super::compact::ConstraintStore;
    use super::super::{LinearCombination, Variable};
    use crate::bppp::{
        CircuitProof, Component, Pole, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness, Slot,
        SparseMatrix, TuplePole,
    };
    use crate::errors::R1CSError;

    /// Parse a proof for `|n| = n_m` (`N'_m`), `|l| = 7 + n_lin` (spec §6.2).
    pub(crate) fn proof_from_bytes_shape(bytes: &[u8], n_m: usize, n_lin: usize) -> Result<CircuitProof, R1CSError> {
        if n_m == 0 {
            return Err(R1CSError::FormatError);
        }
        CircuitProof::from_bytes_dims(bytes, n_lin, n_m).map_err(|_| R1CSError::FormatError)
    }

    /// The prover's values of the variables (spec §7.6).
    pub(crate) struct Values<'a> {
        pub(crate) a_l: &'a [Scalar],
        pub(crate) a_r: &'a [Scalar],
        pub(crate) a_o: &'a [Scalar],
        pub(crate) v: &'a [Scalar],
        pub(crate) s: &'a [Scalar],
        pub(crate) w: &'a [Scalar],
    }

    impl<'a> Values<'a> {
        fn var(&self, x: Variable) -> Scalar {
            match x {
                Variable::MultiplierLeft(i) => self.a_l[i],
                Variable::MultiplierRight(i) => self.a_r[i],
                Variable::MultiplierOutput(i) => self.a_o[i],
                Variable::Committed(j) => self.v[j],
                Variable::Witness(i) => self.w[i],
                Variable::One() => Scalar::ONE,
            }
        }

        fn lc(&self, lc: &LinearCombination) -> Scalar {
            lc.terms.iter().map(|(x, c)| c * self.var(*x)).sum()
        }
    }

    /// The builder's record after finalization (spec §7.4).
    pub(crate) struct Record<'a> {
        /// R1CS multipliers and committed inputs.
        pub(crate) n: usize,
        pub(crate) k: usize,
        /// Witnesses, multiplicities included.
        pub(crate) n_w: usize,
        pub(crate) products: &'a [(LinearCombination, LinearCombination, LinearCombination)],
        pub(crate) args: &'a [Argument],
    }

    fn has_right(lc: &LinearCombination) -> bool {
        lc.terms.iter().any(|(x, _)| matches!(x, Variable::MultiplierRight(_)))
    }

    /// The reciprocal form circuit of the builder's record (spec §7.6) and, with `values`
    /// (the prover), its witness. The prover's R1CS constraints have no constants: they are
    /// recomputed from the witness, as in §6.
    pub(crate) fn builder_circuit(
        store: &ConstraintStore,
        rec: &Record,
        values: Option<&Values>,
    ) -> Result<(ReciprocalCircuit, Option<ReciprocalWitness>), R1CSError> {
        let (n, k, n_w) = (rec.n, rec.k, rec.n_w);
        let n_p: usize = rec.args.iter().map(|a| a.private.len()).sum();
        let n_prod = rec.products.len();
        let n_r = if n == 0 && n_prod == 0 && n_p == 0 { 1 } else { n };
        let n_m = n_r + n_prod;
        let n_mm = n_p + n_m;

        // Copies of numerators and public coefficients that read w_R, and of tuple components
        // (m >= 2) that read w_L or w_R (spec §7.6): per argument, per private term the
        // numerator then the components, then the public terms.
        let mut copies: Vec<&LinearCombination> = Vec::new();
        let mut num_copy = Vec::with_capacity(n_p);
        let mut comp_copy: Vec<Vec<Option<usize>>> = Vec::with_capacity(n_p);
        let mut pub_copy = Vec::with_capacity(rec.args.len());
        for a in rec.args {
            for (num, tuple) in &a.private {
                num_copy.push(if has_right(num) {
                    copies.push(num);
                    Some(copies.len() - 1)
                } else {
                    None
                });
                comp_copy.push(
                    tuple
                        .iter()
                        .map(|x| {
                            if a.m >= 2 && needs_early_copy(x) {
                                copies.push(x);
                                Some(copies.len() - 1)
                            } else {
                                None
                            }
                        })
                        .collect(),
                );
            }
            let mut pc = Vec::with_capacity(a.public.len());
            for (coeff, _) in &a.public {
                pc.push(if has_right(coeff) {
                    copies.push(coeff);
                    Some(copies.len() - 1)
                } else {
                    None
                });
            }
            pub_copy.push(pc);
        }
        let n_o = n_r + k + n_w + copies.len();
        let n_lin = n_o.saturating_sub(n_mm);
        let n_cols = 2 * n_mm + n_o;
        let (col_d, col_l, col_p, col_r) = (|i: usize| i, |i: usize| n_p + i, |i: usize| n_mm + i, |i: usize| n_mm + n_p + i);
        let col_o = |e: usize| 2 * n_mm + e;
        let col_copy = |q: usize| col_o(n_r + k + n_w + q);
        let unknown = || gadget_error("a constraint uses a variable outside the constraint system");
        let col = |x: Variable| -> Result<usize, R1CSError> {
            match x {
                Variable::MultiplierLeft(i) if i < n => Ok(col_l(i)),
                Variable::MultiplierRight(i) if i < n => Ok(col_r(i)),
                Variable::MultiplierOutput(i) if i < n => Ok(col_o(i)),
                Variable::Committed(j) if j < k => Ok(col_o(n_r + j)),
                Variable::Witness(i) if i < n_w => Ok(col_o(n_r + k + i)),
                _ => Err(unknown()),
            }
        };
        // An LC as (column, scaled coefficient) terms in order and its scaled constant.
        let lower = |lc: &LinearCombination, scale: Scalar| -> Result<(Vec<(usize, Scalar)>, Scalar), R1CSError> {
            let mut terms = Vec::with_capacity(lc.terms.len());
            let mut constant = Scalar::ZERO;
            for (x, c) in &lc.terms {
                match x {
                    Variable::One() => constant += c * scale,
                    _ => terms.push((col(*x)?, c * scale)),
                }
            }
            Ok((terms, constant))
        };

        // Numerators.
        let mut w_n = SparseMatrix::new(n_cols);
        let mut a_n = Vec::with_capacity(n_p);
        let mut pole = 0;
        for a in rec.args {
            for (num, _) in &a.private {
                match num_copy[pole] {
                    Some(q) => {
                        w_n.push_row(vec![(col_copy(q), Scalar::ONE)]);
                        a_n.push(Scalar::ZERO);
                    }
                    None => {
                        let (t, c) = lower(num, Scalar::ONE)?;
                        w_n.push_row(t);
                        a_n.push(c);
                    }
                }
                pole += 1;
            }
        }

        // Multiplicative rows.
        let mut w_m = SparseMatrix::new(n_cols);
        let mut a_m = Vec::with_capacity(n_m);
        for i in 0..n_r {
            w_m.push_row(vec![(col_o(i), Scalar::ONE)]);
            a_m.push(Scalar::ZERO);
        }
        for (_, _, out) in rec.products {
            let (t, c) = lower(out, Scalar::ONE)?;
            w_m.push_row(t);
            a_m.push(c);
        }

        // Linear rows.
        let mut w_l = SparseMatrix::new(n_cols);
        let mut a_l = Vec::new();
        for j in 0..k {
            w_l.push_row(vec![(col_o(n_r + j), -Scalar::ONE)]);
            a_l.push(Scalar::ZERO);
        }
        for q in 0..store.len() {
            let mut terms = Vec::new();
            let mut constant = Scalar::ZERO;
            for (x, c) in store.row(q) {
                match (x, values) {
                    (Variable::One(), _) => constant += c,
                    (_, v) => {
                        terms.push((col(x)?, c));
                        if let Some(v) = v {
                            constant -= c * v.var(x);
                        }
                    }
                }
            }
            w_l.push_row(terms);
            a_l.push(constant);
        }
        let neg = -Scalar::ONE;
        let push_eq = |w_l: &mut SparseMatrix, a_l: &mut Vec<Scalar>, first: usize, lc: &LinearCombination| -> Result<(), R1CSError> {
            let (t, c) = lower(lc, neg)?;
            w_l.push_row(core::iter::once((first, Scalar::ONE)).chain(t));
            a_l.push(c);
            Ok(())
        };
        for (g, (l, r, _)) in rec.products.iter().enumerate() {
            push_eq(&mut w_l, &mut a_l, col_l(n_r + g), l)?;
            push_eq(&mut w_l, &mut a_l, col_r(n_r + g), r)?;
        }
        // Poles of one-column arguments: w_D,i - x_0 = 0. Poles of arguments with m >= 2 are
        // tuple poles (spec §4.1), over early columns.
        let mut tuples = Vec::new();
        let mut pole = 0;
        for a in rec.args {
            for (_, tuple) in &a.private {
                if a.m == 1 {
                    push_eq(&mut w_l, &mut a_l, col_d(pole), &tuple[0])?;
                } else {
                    let mut components = Vec::with_capacity(a.m);
                    for (x, copy) in tuple.iter().zip(&comp_copy[pole]) {
                        components.push(match copy {
                            Some(q) => Component { terms: vec![(col_copy(*q), Scalar::ONE)], constant: Scalar::ZERO },
                            None => {
                                let (terms, constant) = lower(x, Scalar::ONE)?;
                                Component { terms, constant }
                            }
                        });
                    }
                    tuples.push(TuplePole { pole, components });
                }
                pole += 1;
            }
        }
        for (q, u) in copies.iter().enumerate() {
            push_eq(&mut w_l, &mut a_l, col_copy(q), u)?;
        }

        // Reciprocal rows.
        let mut recip = Vec::with_capacity(rec.args.len());
        let mut pole = 0;
        for (a, pc) in rec.args.iter().zip(&pub_copy) {
            let mut terms = Vec::new();
            let mut consts = Vec::new();
            for _ in &a.private {
                terms.push((col_p(pole), Scalar::ONE, None));
                pole += 1;
            }
            for ((coeff, row), copy) in a.public.iter().zip(pc) {
                let t = Some(Pole(row.iter().map(|e| Scalar::from(*e)).collect()));
                match copy {
                    Some(q) => terms.push((col_copy(*q), Scalar::ONE, t)),
                    None => {
                        let (lt, c) = lower(coeff, Scalar::ONE)?;
                        terms.extend(lt.into_iter().map(|(col, v)| (col, v, t.clone())));
                        if coeff.terms.iter().any(|(x, _)| *x == Variable::One()) {
                            consts.push((c, t));
                        }
                    }
                }
            }
            recip.push(ReciprocalRow { terms, consts });
        }

        let partition = (0..n_o).map(|e| if e < n_mm { (Slot::NormO, e) } else { (Slot::LinO, e - n_mm) }).collect();
        let circuit = ReciprocalCircuit {
            n_p,
            n_m,
            n_o,
            n_v: 1,
            n_lin,
            k,
            w_n,
            a_n,
            w_m,
            a_m,
            w_l,
            a_l,
            recip,
            tuples,
            f_l: k > 0,
            f_m: false,
            partition,
        };

        let witness = values.map(|v| {
            let mut w_d = Vec::with_capacity(n_p);
            for a in rec.args {
                for (_, tuple) in &a.private {
                    // a tuple pole is set by the prover after eta (spec §4.3)
                    w_d.push(if a.m == 1 { v.lc(&tuple[0]) } else { Scalar::ZERO });
                }
            }
            let pad = |x: &[Scalar]| -> Vec<Scalar> {
                let mut out = x.to_vec();
                out.resize(n_r, Scalar::ZERO);
                out
            };
            let mut w_l = pad(v.a_l);
            let mut w_r = pad(v.a_r);
            for (l, r, _) in rec.products {
                w_l.push(v.lc(l));
                w_r.push(v.lc(r));
            }
            let w_o: Vec<Scalar> =
                pad(v.a_o).into_iter().chain(v.v.iter().copied()).chain(v.w.iter().copied()).chain(copies.iter().map(|u| v.lc(u))).collect();
            ReciprocalWitness { w_d, w_l, w_r, w_o, v: v.v.iter().map(|x| vec![*x]).collect(), s: v.s.to_vec() }
        });
        Ok((circuit, witness))
    }
}

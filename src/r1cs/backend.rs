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

    use super::super::builder::{gadget_error, offsets, pack_row, pow2, Argument};
    use super::super::compact::ConstraintStore;
    use super::super::{LinearCombination, Variable};
    use crate::bppp::{
        ArithmeticCircuit, CircuitProof, CircuitWitness, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness, Slot,
        SparseMatrix,
    };
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
                        Variable::Witness(_) | Variable::One() => Scalar::ZERO,
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

    /// Parse a circuit proof for `|n| = n_m`, `|l| = 7 + n_lin` (a translated R1CS has
    /// `n_lin = k`).
    pub(crate) fn proof_from_bytes_shape(bytes: &[u8], n_m: usize, n_lin: usize) -> Result<CircuitProof, R1CSError> {
        let k = n_lin;
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

        // Copies of numerators and public coefficients that read w_R.
        let mut copies: Vec<&LinearCombination> = Vec::new();
        let mut num_copy = Vec::with_capacity(n_p);
        let mut pub_copy = Vec::with_capacity(rec.args.len());
        for a in rec.args {
            for (num, _) in &a.private {
                num_copy.push(if has_right(num) {
                    copies.push(num);
                    Some(copies.len() - 1)
                } else {
                    None
                });
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
        let mut pole = 0;
        for a in rec.args {
            let o = offsets(&a.widths);
            for (_, tuple) in &a.private {
                let mut terms = vec![(col_d(pole), Scalar::ONE)];
                let mut constant = Scalar::ZERO;
                for (x, oj) in tuple.iter().zip(&o) {
                    let (t, c) = lower(x, -pow2(*oj))?;
                    terms.extend(t);
                    constant += c;
                }
                w_l.push_row(terms);
                a_l.push(constant);
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
                let t = Some(pack_row(row, &a.widths));
                match copy {
                    Some(q) => terms.push((col_copy(*q), Scalar::ONE, t)),
                    None => {
                        let (lt, c) = lower(coeff, Scalar::ONE)?;
                        terms.extend(lt.into_iter().map(|(col, v)| (col, v, t)));
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
            f_l: k > 0,
            f_m: false,
            partition,
        };

        let witness = values.map(|v| {
            let mut w_d = Vec::with_capacity(n_p);
            for a in rec.args {
                let o = offsets(&a.widths);
                for (_, tuple) in &a.private {
                    w_d.push(tuple.iter().zip(&o).map(|(x, oj)| pow2(*oj) * v.lc(x)).sum());
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

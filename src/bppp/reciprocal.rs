//! Reciprocal form circuits (spec §4, paper §6.2–6.3).
//!
//! An arithmetic circuit with `n_p` poles: private denominators `w_D` committed with the
//! initial witness, reciprocals `w_P,i = num_i / (alpha + w_D,i)` committed after the challenge
//! `alpha`, and reciprocal rows that must vanish as rational functions. For a fixed `alpha` the
//! circuit compiles to an [`ArithmeticCircuit`] proven with the inner protocol of spec §3.
//!
//! Tuple poles (spec §4.1, our extension): `w_D,i = sum_j eta^j x_ij` with components in `C_O`,
//! committed before a challenge `eta`; public poles are then polynomials in `eta`. A circuit
//! that uses `eta` is proven with protocol v2 (`C_O`, `eta`, `C_L`, `alpha`, `C_R`).

use alloc::vec;
use alloc::vec::Vec;

use ff::Field as _;
use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroize;

use super::circuit::{self, ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
use super::gens::BpppGens;
use super::sparse::{BufHasher, SparseMatrix};
use super::transcript::BpppTranscript;
use crate::curve::{Curve, Field};
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// A public pole (spec §4.1): a polynomial in the challenge `eta`, `t(eta) = sum_e t_e eta^e`;
/// a circuit needs at least one coefficient (`check` rejects an empty one), and one coefficient
/// is a constant pole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pole<F: Field>(pub Vec<F>);

impl<F: Field> From<F> for Pole<F> {
    fn from(t: F) -> Self {
        Pole(vec![t])
    }
}

impl<F: Field> Pole<F> {
    /// `t(eta)` (Horner).
    pub fn eval(&self, eta: F) -> F {
        self.0.iter().rev().fold(F::ZERO, |acc, t| acc * eta + t)
    }
}

/// A reciprocal row (spec §4.1): `sum c * w'[col] / (X + t)` over the terms (no pole: `c *
/// w'[col]`) plus `sum c / (X + t)` over the constants (no pole: `c`), which must vanish.
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalRow<F: Field> {
    /// `(column of w', coefficient, pole)`.
    pub terms: Vec<(usize, F, Option<Pole<F>>)>,
    /// `(coefficient, pole)`.
    pub consts: Vec<(F, Option<Pole<F>>)>,
}

/// A component of a tuple pole: `sum c * w'[col] + constant` over early columns (`w_O` in
/// slots `NormO`, `LinO`).
#[derive(Clone, Debug, PartialEq)]
pub struct Component<F: Field> {
    /// `(column of w', coefficient)`.
    pub terms: Vec<(usize, F)>,
    /// The constant.
    pub constant: F,
}

/// A tuple pole (spec §4.1): `w_D,pole = sum_j eta^j x_j`, computed by the prover after `eta`
/// (the witness's value for it is ignored).
#[derive(Clone, Debug, PartialEq)]
pub struct TuplePole<F: Field> {
    /// The pole, `< n_p`.
    pub pole: usize,
    /// The components `x_0, x_1, ...` (at least one).
    pub components: Vec<Component<F>>,
}

/// A reciprocal form circuit (spec §4.1). Columns index
/// `w' = w_D || w_L || w_P || w_R || w_O`.
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalCircuit<F: Field> {
    /// Number of poles.
    pub n_p: usize,
    /// Number of ordinary multiplications.
    pub n_m: usize,
    /// `|w_O|`.
    pub n_o: usize,
    /// Length of each input vector.
    pub n_v: usize,
    /// Length of the linear part of the commitments.
    pub n_lin: usize,
    /// Number of input vectors.
    pub k: usize,
    /// Numerators, `n_p` rows over initial columns only.
    pub w_n: SparseMatrix<F>,
    /// Affine term of the numerators.
    pub a_n: Vec<F>,
    /// Ordinary multiplicative constraints, `n_m` rows.
    pub w_m: SparseMatrix<F>,
    /// Affine term of the ordinary multiplicative constraints.
    pub a_m: Vec<F>,
    /// Ordinary linear constraints.
    pub w_l: SparseMatrix<F>,
    /// Affine term of the ordinary linear constraints.
    pub a_l: Vec<F>,
    /// Reciprocal rows.
    pub recip: Vec<ReciprocalRow<F>>,
    /// Tuple poles, in increasing pole order (spec §4.1); empty for a circuit of the paper.
    pub tuples: Vec<TuplePole<F>>,
    /// Inputs enter the first `k n_v` ordinary linear rows.
    pub f_l: bool,
    /// Inputs enter the first `k n_v` compiled multiplicative rows (numerators first).
    pub f_m: bool,
    /// Slot of each element of `w_O`.
    pub partition: Vec<(Slot, usize)>,
}

/// A witness for a [`ReciprocalCircuit`]; the reciprocals `w_P` are computed by the prover.
/// Its `Debug` shows only the dimensions.
#[derive(Clone)]
pub struct ReciprocalWitness<F: Field> {
    /// The poles.
    pub w_d: Vec<F>,
    /// Left inputs of the ordinary multiplications.
    pub w_l: Vec<F>,
    /// Right inputs of the ordinary multiplications.
    pub w_r: Vec<F>,
    /// Further witness elements.
    pub w_o: Vec<F>,
    /// The input vectors.
    pub v: Vec<Vec<F>>,
    /// Blindings of the input commitments.
    pub s: Vec<F>,
}

impl<F: Field> ReciprocalWitness<F> {
    /// Overwrite every value with zero (the secrets of a prover that is done with them).
    pub(crate) fn clear(&mut self) {
        for x in self.w_d.iter_mut().chain(&mut self.w_l).chain(&mut self.w_r).chain(&mut self.w_o).chain(&mut self.s) {
            x.zeroize();
        }
        self.v.iter_mut().flatten().for_each(Zeroize::zeroize);
    }
}

impl<F: Field> core::fmt::Debug for ReciprocalWitness<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ReciprocalWitness {{ n_p: {}, n_m: {}, n_o: {} }}", self.w_d.len(), self.w_l.len(), self.w_o.len())
    }
}

/// Where a column of `w'` lives.
#[derive(Clone, Copy, PartialEq)]
enum Col {
    /// Committed before `alpha`.
    Initial,
    /// A reciprocal `w_P,i`.
    Reciprocal(usize),
    /// Committed after `alpha` (`w_R`, `LinR` slots).
    Late,
}

impl<F: Field> ReciprocalCircuit<F> {
    /// The same circuit over another field, every scalar mapped by `f` (the Simplicity
    /// compiler traces the verifier over constants of the circuit).
    #[cfg(feature = "simplicity")]
    pub(crate) fn map_scalars<G: Field>(&self, f: impl Fn(F) -> G + Copy) -> ReciprocalCircuit<G> {
        let pole = |p: &Option<Pole<F>>| p.as_ref().map(|p| Pole(p.0.iter().map(|x| f(*x)).collect()));
        ReciprocalCircuit {
            n_p: self.n_p,
            n_m: self.n_m,
            n_o: self.n_o,
            n_v: self.n_v,
            n_lin: self.n_lin,
            k: self.k,
            w_n: self.w_n.map(f),
            a_n: self.a_n.iter().map(|x| f(*x)).collect(),
            w_m: self.w_m.map(f),
            a_m: self.a_m.iter().map(|x| f(*x)).collect(),
            w_l: self.w_l.map(f),
            a_l: self.a_l.iter().map(|x| f(*x)).collect(),
            recip: self
                .recip
                .iter()
                .map(|r| ReciprocalRow {
                    terms: r.terms.iter().map(|(c, v, p)| (*c, f(*v), pole(p))).collect(),
                    consts: r.consts.iter().map(|(v, p)| (f(*v), pole(p))).collect(),
                })
                .collect(),
            tuples: self
                .tuples
                .iter()
                .map(|t| TuplePole {
                    pole: t.pole,
                    components: t.components.iter().map(|c| Component { terms: c.terms.iter().map(|(i, v)| (*i, f(*v))).collect(), constant: f(c.constant) }).collect(),
                })
                .collect(),
            f_l: self.f_l,
            f_m: self.f_m,
            partition: self.partition.clone(),
        }
    }

    fn n_mm(&self) -> usize {
        self.n_p + self.n_m
    }

    /// The generators of this circuit ([`BpppGens::new`] with `n_lin` and `n_p + n_m`).
    pub fn gens<'a, C: Curve<Scalar = F>>(&self, pc: &PedersenGens<C>, bp: &'a BulletproofGens<C>) -> Result<BpppGens<'a, C>, ProofError> {
        BpppGens::new(pc, bp, self.n_lin, self.n_p.checked_add(self.n_m).ok_or(ProofError::InvalidGeneratorsLength)?)
    }

    /// The `BulletproofGens` capacity [`ReciprocalCircuit::gens`] needs.
    pub fn gens_capacity(&self) -> usize {
        super::gens::capacity(self.n_lin, self.n_p.saturating_add(self.n_m))
    }

    /// Whether the circuit uses the challenge `eta` (spec §4.1): a tuple pole, or a public pole
    /// with two or more coefficients. Only then is it proven with protocol v2.
    pub fn uses_eta(&self) -> bool {
        let long = |p: &Option<Pole<F>>| p.as_ref().map_or(false, |p| p.0.len() > 1);
        !self.tuples.is_empty()
            || self.recip.iter().any(|r| r.terms.iter().any(|t| long(&t.2)) || r.consts.iter().any(|t| long(&t.1)))
    }

    /// Whether column `c` is early (committed in `C_O`: `w_O` in slots `NormO`, `LinO`).
    fn is_early(&self, c: usize) -> bool {
        let n_mm = self.n_mm();
        c >= 2 * n_mm && matches!(self.partition.get(c - 2 * n_mm), Some((Slot::NormO, _)) | Some((Slot::LinO, _)))
    }

    /// `w_D` with the tuple poles set for `eta` (spec §4.3); the components read `w_O` only.
    fn poles_at(&self, w: &ReciprocalWitness<F>, eta: F) -> Vec<F> {
        let mut w_d = w.w_d.clone();
        let base = 2 * self.n_mm();
        for tp in &self.tuples {
            let mut acc = F::ZERO;
            for x in tp.components.iter().rev() {
                let v: F = x.terms.iter().map(|(c, k)| *k * w.w_o[c - base]).sum::<F>() + x.constant;
                acc = acc * eta + v;
            }
            w_d[tp.pole] = acc;
        }
        w_d
    }

    /// The witness with the tuple poles set for `eta` (a copy only if there are tuple poles).
    fn at_eta<'w>(&self, w: &'w ReciprocalWitness<F>, eta: F) -> alloc::borrow::Cow<'w, ReciprocalWitness<F>> {
        if self.tuples.is_empty() {
            alloc::borrow::Cow::Borrowed(w)
        } else {
            let mut x = w.clone();
            x.w_d = self.poles_at(w, eta);
            alloc::borrow::Cow::Owned(x)
        }
    }

    fn dims(&self) -> [u64; 10] {
        [
            self.n_p,
            self.n_m,
            self.n_o,
            self.n_v,
            self.n_lin,
            self.k,
            self.w_l.n_rows(),
            self.recip.len(),
            self.f_l as usize,
            self.f_m as usize,
        ]
        .map(|x| x as u64)
    }

    fn col(&self, c: usize) -> Col {
        let n_mm = self.n_mm();
        if c < n_mm {
            Col::Initial
        } else if c < n_mm + self.n_p {
            Col::Reciprocal(c - n_mm)
        } else if c < 2 * n_mm {
            Col::Late
        } else {
            match self.partition.get(c - 2 * n_mm) {
                Some((Slot::LinR, _)) | None => Col::Late,
                Some(_) => Col::Initial,
            }
        }
    }

    /// Check the shape, the rules of spec §4.1 (numerators and pole terms on initial columns
    /// only) and the shape of the compiled circuit.
    pub fn check(&self) -> Result<(), ProofError> {
        self.check_rules()?;
        // the compiled circuit (spec §4.2) has n_p + n_m multiplications, the rows of W_l, one
        // row per tuple pole and one per reciprocal row, and the matrices checked above (its
        // n_l >= rows of W_l, so the f_l bound on n_l is implied by check_rules; kept for
        // agreement with ArithmeticCircuit::check)
        let n_l = self.w_l.n_rows().checked_add(self.tuples.len()).and_then(|x| x.checked_add(self.recip.len()));
        let shape = circuit::Shape {
            n_m: self.n_mm(),
            n_o: self.n_o,
            n_v: self.n_v,
            n_lin: self.n_lin,
            k: self.k,
            n_l: n_l.ok_or(ProofError::FormatError)?,
            f_l: self.f_l,
            f_m: self.f_m,
        };
        shape.check(&self.partition)
    }

    /// [`ReciprocalCircuit::check`] by compiling the circuit with dummy coefficients and
    /// checking the result (the definition the shape check above must agree with).
    #[cfg(test)]
    pub(crate) fn check_by_compiling(&self) -> Result<(), ProofError> {
        self.check_rules()?;
        self.compile_with(|t: &[F]| Some(vec![F::ONE; t.len()]), F::ONE, F::ONE)?.check()
    }

    /// The shape of the matrices and the rules of spec §4.1.
    fn check_rules(&self) -> Result<(), ProofError> {
        let bad = Err(ProofError::FormatError);
        let n_mm = self.n_p.checked_add(self.n_m).ok_or(ProofError::FormatError)?;
        let n_w = n_mm.checked_mul(2).and_then(|x| x.checked_add(self.n_o)).ok_or(ProofError::FormatError)?;
        if self.w_n.n_cols() != n_w || self.w_n.n_rows() != self.n_p || self.a_n.len() != self.n_p {
            return bad;
        }
        if self.w_m.n_cols() != n_w || self.w_m.n_rows() != self.n_m || self.a_m.len() != self.n_m {
            return bad;
        }
        if self.w_l.n_cols() != n_w || self.a_l.len() != self.w_l.n_rows() {
            return bad;
        }
        // the partition is checked by the compiled circuit; col() needs its length
        if self.partition.len() != self.n_o {
            return bad;
        }
        // f_l puts the inputs on the ordinary linear rows only, never on reciprocal rows
        let kv = self.k.checked_mul(self.n_v).ok_or(ProofError::FormatError)?;
        if self.f_l && self.w_l.n_rows() < kv {
            return bad;
        }
        for r in 0..self.n_p {
            if self.w_n.row(r).any(|(c, _)| self.col(c) != Col::Initial) {
                return bad;
            }
        }
        let empty = |p: &Option<Pole<F>>| p.as_ref().map_or(false, |p| p.0.is_empty());
        for row in &self.recip {
            for (c, _, pole) in &row.terms {
                let ok = *c < n_w
                    && !empty(pole)
                    && match (self.col(*c), pole) {
                        (Col::Initial, _) => true,
                        (Col::Reciprocal(_), None) => true,
                        _ => false,
                    };
                if !ok {
                    return bad;
                }
            }
            if row.consts.iter().any(|(_, p)| empty(p)) {
                return bad;
            }
        }
        // tuple poles: increasing, in range, components on early columns only
        let mut next = 0;
        for tp in &self.tuples {
            if tp.pole < next || tp.pole >= self.n_p || tp.components.is_empty() {
                return bad;
            }
            next = tp.pole + 1;
            if tp.components.iter().any(|x| x.terms.iter().any(|(c, _)| !self.is_early(*c))) {
                return bad;
            }
        }
        // free and tuple poles do not mix in an eta-row (spec §4.1); tuples are sorted
        let is_tuple = |i: usize| self.tuples.binary_search_by_key(&i, |tp| tp.pole).is_ok();
        let long = |p: &Option<Pole<F>>| p.as_ref().map_or(false, |p| p.0.len() > 1);
        for row in &self.recip {
            let mut free = false;
            let mut eta_row = row.consts.iter().any(|(_, p)| long(p));
            for (c, _, p) in &row.terms {
                eta_row |= long(p);
                if let Col::Reciprocal(i) = self.col(*c) {
                    if is_tuple(i) {
                        eta_row = true;
                    } else {
                        free = true;
                    }
                }
            }
            if eta_row && free {
                return bad;
            }
        }
        Ok(())
    }

    /// The compiled circuit, with `coef(t)` the factors of the terms with poles of values `t`
    /// (in row order: terms, then constants; `None` when one is undefined), `alpha` the
    /// coefficient subtracted at the reciprocal columns, and `eta` the challenge of the tuple
    /// poles and pole polynomials.
    fn compile_with<CF: FnOnce(&[F]) -> Option<Vec<F>>>(&self, coef: CF, alpha: F, eta: F) -> Result<ArithmeticCircuit<F>, ProofError> {
        let n_mm = self.n_mm();
        let n_w = 2 * n_mm + self.n_o;
        let mut w_m = SparseMatrix::new(n_w);
        for i in 0..self.n_p {
            w_m.push_row(self.w_n.row(i).map(|(c, v)| (c, *v)).chain(Some((n_mm + i, -alpha))));
        }
        w_m.extend_rows(&self.w_m);
        // check() has made the widths of w_m and w_l n_w
        let mut w_l = self.w_l.clone();
        let mut a_l = self.a_l.clone();
        // w_D,i - sum_j eta^j x_ij = 0, built in parallel chunks (the same rows, in order)
        let m_max = self.tuples.iter().map(|tp| tp.components.len()).max().unwrap_or(0);
        let pows: Vec<F> = core::iter::successors(Some(F::ONE), |e| Some(*e * eta)).take(m_max).collect();
        const CHUNK: usize = 4096;
        let n_t = self.tuples.len();
        let build = |k: usize| {
            let mut m = SparseMatrix::new(n_w);
            let mut a: Vec<F> = Vec::with_capacity(CHUNK);
            for tp in &self.tuples[k * CHUNK..((k + 1) * CHUNK).min(n_t)] {
                let components = || tp.components.iter().zip(&pows);
                m.push_row(core::iter::once((tp.pole, F::ONE)).chain(components().flat_map(|(x, e)| x.terms.iter().map(move |(c, v)| (*c, -*e * v)))));
                a.push(components().map(|(x, e)| -(*e * x.constant)).sum());
            }
            (m, a)
        };
        crate::util::map_in_order((n_t + CHUNK - 1) / CHUNK, build, |(m, a)| {
            w_l.extend_rows(&m);
            a_l.extend(a);
        });
        // the factors of all terms with a pole, in row order (terms, then constants), at once
        let poles = || self.recip.iter().flat_map(|row| row.terms.iter().map(|(_, _, p)| p).chain(row.consts.iter().map(|(_, p)| p)));
        let values: Vec<F> = poles().flatten().map(|t| t.eval(eta)).collect();
        let factors = coef(&values).ok_or(ProofError::VerificationError)?;
        debug_assert_eq!(factors.len(), values.len());
        drop(values);
        let mut factors = factors.into_iter();
        let mut factor = |pole: &Option<Pole<F>>| pole.as_ref().map_or(F::ONE, |_| factors.next().expect("one factor per pole"));
        for row in &self.recip {
            let terms: Vec<(usize, F)> = row.terms.iter().map(|(c, v, pole)| (*c, *v * factor(pole))).collect();
            w_l.push_row(terms);
            let a = row.consts.iter().map(|(v, pole)| *v * factor(pole)).sum();
            a_l.push(a);
        }
        Ok(ArithmeticCircuit {
            n_m: n_mm,
            n_o: self.n_o,
            n_v: self.n_v,
            n_lin: self.n_lin,
            k: self.k,
            w_l,
            a_l,
            w_m,
            a_m: self.a_n.iter().chain(&self.a_m).copied().collect(),
            f_l: self.f_l,
            f_m: self.f_m,
            partition: self.partition.clone(),
        })
    }

    /// The compiled circuit for the challenges `eta` (ignored by a circuit that does not use
    /// it) and `alpha` (spec §4.2); an error if a public pole has `alpha + t(eta) = 0`.
    fn compile(&self, eta: F, alpha: F) -> Result<ArithmeticCircuit<F>, ProofError> {
        // 1 / (alpha + t) for every pole value t, by one batch inversion (public values)
        let inverses = |t: &[F]| {
            let mut d: Vec<F> = t.iter().map(|t| alpha + t).collect();
            if d.iter().any(|d| *d == F::ZERO) {
                return None;
            }
            F::batch_invert(&mut d);
            Some(d)
        };
        self.compile_with(inverses, alpha, eta)
    }

    /// The reciprocal circuit digest (spec §4.4).
    pub fn digest(&self) -> [u8; 32] {
        let v2 = self.uses_eta();
        let mut h = BufHasher::new();
        h.update(if v2 { &b"bppp-reciprocal-digest v2"[..] } else { &b"bppp-reciprocal-digest v1"[..] });
        for x in self.dims() {
            h.update(x.to_le_bytes());
        }
        if v2 {
            h.update((self.tuples.len() as u64).to_le_bytes());
        }
        for &(slot, t) in &self.partition {
            h.update([slot as u8]);
            h.update((t as u64).to_le_bytes());
        }
        self.w_n.hash_into(&mut h);
        self.w_m.hash_into(&mut h);
        self.w_l.hash_into(&mut h);
        for a in self.a_n.iter().chain(&self.a_m).chain(&self.a_l) {
            h.update(a.to_bytes32());
        }
        let pole = |h: &mut BufHasher, p: &Option<Pole<F>>| match p {
            None => h.update([0u8]),
            Some(t) => {
                h.update([1u8]);
                if v2 {
                    h.update((t.0.len() as u64).to_le_bytes());
                    t.0.iter().for_each(|x| h.update(x.to_bytes32()));
                } else {
                    t.0.iter().for_each(|x| h.update(x.to_bytes32())); // one coefficient
                }
            }
        };
        for row in &self.recip {
            h.update((row.terms.len() as u64).to_le_bytes());
            for (c, v, p) in &row.terms {
                h.update((*c as u64).to_le_bytes());
                h.update(v.to_bytes32());
                pole(&mut h, p);
            }
            h.update((row.consts.len() as u64).to_le_bytes());
            for (v, p) in &row.consts {
                h.update(v.to_bytes32());
                pole(&mut h, p);
            }
        }
        for tp in &self.tuples {
            h.update((tp.pole as u64).to_le_bytes());
            h.update((tp.components.len() as u64).to_le_bytes());
            for x in &tp.components {
                h.update((x.terms.len() as u64).to_le_bytes());
                for (c, v) in &x.terms {
                    h.update((*c as u64).to_le_bytes());
                    h.update(v.to_bytes32());
                }
                h.update(x.constant.to_bytes32());
            }
        }
        h.finalize()
    }

    fn check_witness(&self, w: &ReciprocalWitness<F>) -> Result<(), ProofError> {
        if w.w_d.len() != self.n_p
            || w.w_l.len() != self.n_m
            || w.w_r.len() != self.n_m
            || w.w_o.len() != self.n_o
            || w.v.len() != self.k
            || w.s.len() != self.k
            || w.v.iter().any(|v| v.len() != self.n_v)
        {
            return Err(ProofError::FormatError);
        }
        Ok(())
    }

    /// `w'` with the reciprocal columns set to `w_p`.
    fn full(&self, w: &ReciprocalWitness<F>, w_p: &[F]) -> Vec<F> {
        w.w_d.iter().chain(&w.w_l).chain(w_p).chain(&w.w_r).chain(&w.w_o).copied().collect()
    }

    /// The numerators `(W_n w' + f_m w_V + a_n)_i` (initial columns only, so `w_P` is not needed).
    fn numerators(&self, w: &ReciprocalWitness<F>) -> Vec<F> {
        let full = self.full(w, &vec![F::ZERO; self.n_p]);
        let w_v: Vec<F> = w.v.iter().flatten().copied().collect();
        let f_m = if self.f_m { F::ONE } else { F::ZERO };
        self.w_n
            .mul_vec(&full)
            .iter()
            .zip(&self.a_n)
            .enumerate()
            .map(|(i, (x, a))| *x + a + f_m * w_v.get(i).copied().unwrap_or(F::ZERO))
            .collect()
    }

    /// Whether `w` satisfies the circuit for the challenges `eta` (ignored by a circuit that
    /// does not use it) and `alpha` (spec §4.1): with the tuple poles set for `eta`, every
    /// reciprocal row vanishes as a rational function of `X` (all multiplicities per pole value
    /// and the polynomial part are zero), and the compiled circuit holds (for rows that read
    /// reciprocals).
    pub fn is_satisfied(&self, w: &ReciprocalWitness<F>, eta: F, alpha: F) -> bool {
        if self.check().is_err() || self.check_witness(w).is_err() {
            return false;
        }
        let w = &*self.at_eta(w, eta);
        let num = self.numerators(w);
        let full = self.full(w, &vec![F::ZERO; self.n_p]);
        for row in &self.recip {
            let mut poles: Vec<(F, F)> = Vec::new();
            let mut poly = F::ZERO;
            let mut add = |pole: Option<F>, x: F| match pole {
                None => poly += x,
                Some(t) => match poles.iter_mut().find(|(p, _)| *p == t) {
                    Some((_, m)) => *m += x,
                    None => poles.push((t, x)),
                },
            };
            for (c, v, pole) in &row.terms {
                match self.col(*c) {
                    Col::Reciprocal(i) => add(Some(w.w_d[i]), *v * num[i]),
                    _ => add(pole.as_ref().map(|p| p.eval(eta)), *v * full[*c]),
                }
            }
            for (v, pole) in &row.consts {
                add(pole.as_ref().map(|p| p.eval(eta)), *v);
            }
            if poly != F::ZERO || poles.iter().any(|(_, m)| *m != F::ZERO) {
                return false;
            }
        }
        match (self.reciprocals(w, alpha), self.compile(eta, alpha)) {
            (Ok(w_p), Ok(c)) => c.is_satisfied(&self.compiled_witness(w, w_p)),
            _ => false,
        }
    }

    /// `w_P,i = num_i / (alpha + w_D,i)`; an error if a denominator is zero.
    fn reciprocals(&self, w: &ReciprocalWitness<F>, alpha: F) -> Result<Vec<F>, ProofError> {
        // One inversion for all denominators (Montgomery's trick, constant time); a zero
        // denominator would spoil the whole batch, so it is checked first.
        let mut inv: Vec<F> = w.w_d.iter().map(|d| alpha + d).collect();
        let any_zero = inv.iter().fold(subtle::Choice::from(0u8), |acc, d| acc | d.ct_eq(&F::ZERO));
        if bool::from(any_zero) {
            inv.iter_mut().for_each(Zeroize::zeroize);
            return Err(ProofError::VerificationError);
        }
        F::batch_invert(&mut inv);
        let out = self.numerators(w).iter().zip(&inv).map(|(n, i)| *n * i).collect();
        inv.iter_mut().for_each(Zeroize::zeroize);
        Ok(out)
    }

    /// The compiled circuit and witness for `(eta, alpha)` (tests).
    #[cfg(test)]
    pub(crate) fn compiled_for_test(&self, w: &ReciprocalWitness<F>, eta: F, alpha: F) -> (ArithmeticCircuit<F>, CircuitWitness<F>) {
        let w = &*self.at_eta(w, eta);
        let w_p = self.reciprocals(w, alpha).unwrap();
        (self.compile(eta, alpha).unwrap(), self.compiled_witness(w, w_p))
    }

    #[cfg(test)]
    pub(crate) fn reciprocals_for_test(&self, w: &ReciprocalWitness<F>, eta: F, alpha: F) -> Vec<F> {
        self.reciprocals(&self.at_eta(w, eta), alpha).unwrap()
    }

    /// `w_D` with the tuple poles set for `eta` (tests).
    #[cfg(test)]
    pub(crate) fn poles_for_test(&self, w: &ReciprocalWitness<F>, eta: F) -> Vec<F> {
        self.poles_at(w, eta)
    }

    /// The late values given in the witness itself (the one-phase prover).
    fn given_late(&self, w: &ReciprocalWitness<F>) -> LateWitness<F> {
        LateWitness { w_r: w.w_r.clone(), w_o_late: self.late_elements(&w.w_o) }
    }

    /// The number of `LinR` slots (elements of `w_O` committed after `alpha`).
    fn n_late(&self) -> usize {
        self.partition.iter().filter(|(s, _)| *s == Slot::LinR).count()
    }

    /// The `LinR` elements of `w_o`, in order.
    fn late_elements(&self, w_o: &[F]) -> Vec<F> {
        w_o.iter().zip(&self.partition).filter(|(_, (s, _))| *s == Slot::LinR).map(|(x, _)| *x).collect()
    }

    fn compiled_witness(&self, w: &ReciprocalWitness<F>, w_p: Vec<F>) -> CircuitWitness<F> {
        CircuitWitness {
            w_l: w.w_d.iter().chain(&w.w_l).copied().collect(),
            w_r: w_p.into_iter().chain(w.w_r.iter().copied()).collect(),
            w_o: w.w_o.clone(),
            v: w.v.clone(),
            s: w.s.clone(),
        }
    }
}

/// Absorb the statement (spec §4.4); returns the circuit digest.
fn absorb_statement<C: Curve, T: BpppTranscript + ?Sized>(t: &mut T, c: &ReciprocalCircuit<C::Scalar>, gens: &BpppGens<C>, V: &[C::Compressed]) -> [u8; 32] {
    let v2 = c.uses_eta();
    t.domain_sep(if v2 { b"bppp-reciprocal v2" } else { b"bppp-reciprocal v1" });
    let labels: [&'static [u8]; 10] =
        [b"N_p", b"N_m", b"N_O", b"N_v", b"N_lin", b"k", b"N_l", b"N_r", b"f_l", b"f_m"];
    for (label, x) in labels.iter().zip(c.dims()) {
        t.append_u64(label, x);
    }
    if v2 {
        t.append_u64(b"N_t", c.tuples.len() as u64);
    }
    circuit::absorb_tail(t, gens, c.digest(), V)
}

fn check_gens<C: Curve>(c: &ReciprocalCircuit<C::Scalar>, gens: &BpppGens<C>) -> Result<(), ProofError> {
    gens.check_dims(c.n_lin, c.n_p.checked_add(c.n_m).ok_or(ProofError::InvalidGeneratorsLength)?)
}

/// Prove that `w` satisfies the reciprocal form circuit `c` for the input commitments `V`
/// (spec §4.3). Generators: [`BpppGens::new`] with `n_lin` and `n_p + n_m`. Returns an error if
/// `alpha + w_D,i = 0` (probability `n_p / 2^252`) or the witness does not satisfy `c`.
pub(crate) fn prove<C: Curve, T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    w: &ReciprocalWitness<C::Scalar>,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof<C>, ProofError> {
    prove_checked(c, gens, V, w, transcript, rng, true)
}

/// [`prove`]; with `require_satisfied = false` an unsatisfied witness is proven instead of
/// refused (feature `cheats` of the R1CS front end: such a proof must not verify).
pub(crate) fn prove_checked<C: Curve, T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    w: &ReciprocalWitness<C::Scalar>,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof<C>, ProofError> {
    prove_with(c, gens, V, w, |_, _| Ok(c.given_late(w)), transcript, |t, d| rekeyed(t, c, d, w, rng), require_satisfied)
}

/// The prover's RNG from the transcript, the digest and the initial witness (spec §1; the late
/// values are not known to the two-phase prover before `alpha`, and both provers must agree).
fn rekeyed<F: Field, T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(t: &T, c: &ReciprocalCircuit<F>, digest: &[u8; 32], w: &ReciprocalWitness<F>, rng: &mut R) -> merlin::TranscriptRng {
    let early_o = w.w_o.iter().zip(&c.partition).filter(|(_, (s, _))| *s != Slot::LinR).map(|(x, _)| x);
    // tuple poles are not known before eta: hashed as 0 (spec §1)
    let mut w_d = w.w_d.clone();
    c.tuples.iter().for_each(|tp| w_d[tp.pole] = F::ZERO);
    let secrets = w_d.iter().chain(&w.w_l).chain(early_o).chain(w.v.iter().flatten()).chain(&w.s);
    let r = super::transcript::prover_rng(t, b"reciprocal", digest, secrets, rng);
    w_d.iter_mut().for_each(Zeroize::zeroize);
    r
}

/// The prover with the caller's RNG as is (the reference vectors replay its values), and an
/// unsatisfied witness proven unless `require_satisfied` (tests).
#[cfg(test)]
pub(crate) fn prove_impl<C: Curve, T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    w: &ReciprocalWitness<C::Scalar>,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof<C>, ProofError> {
    prove_with(c, gens, V, w, |_, _| Ok(c.given_late(w)), transcript, |_, _| rng, require_satisfied)
}

/// A proof for a reciprocal form circuit (spec §4); the encoding is that of a
/// [`CircuitProof`] for the compiled circuit (spec §4.6).
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalProof<C: Curve = crate::curve::Ristretto>(pub(crate) CircuitProof<C>);

impl<C: Curve> ReciprocalProof<C> {
    /// Prove that `w` satisfies `c` for the input commitments `V` (spec §4.3). Generators:
    /// [`ReciprocalCircuit::gens`]. An error if `alpha + w_D,i = 0` (probability
    /// `n_p / 2^252`) or if the witness does not satisfy `c`.
    pub fn prove<T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(
        c: &ReciprocalCircuit<C::Scalar>,
        gens: &BpppGens<C>,
        V: &[C::Compressed],
        w: &ReciprocalWitness<C::Scalar>,
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<Self, ProofError> {
        prove(c, gens, V, w, transcript, rng).map(ReciprocalProof)
    }

    /// [`ReciprocalProof::prove`] with the late values (`w_R` and the `LinR` elements of `w_O`)
    /// computed by `late` from `alpha` and the reciprocals `w_P` (spec §4.3), for ordinary rows
    /// that read reciprocals; the late entries of `w` are ignored. Same transcript, randomness
    /// and proof as `prove` given the same values; an error of `late` is returned as is.
    pub fn prove_two_phase<T, R, LF>(
        c: &ReciprocalCircuit<C::Scalar>,
        gens: &BpppGens<C>,
        V: &[C::Compressed],
        w: &ReciprocalWitness<C::Scalar>,
        late: LF,
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<Self, ProofError>
    where
        T: BpppTranscript + ?Sized,
        R: RngCore + CryptoRng,
        LF: FnOnce(C::Scalar, &[C::Scalar]) -> Result<LateWitness<C::Scalar>, ProofError>,
    {
        prove_two_phase(c, gens, V, w, late, transcript, rng).map(ReciprocalProof)
    }

    /// Verify for the circuit `c` and the input commitments `V`.
    pub fn verify<T: BpppTranscript + ?Sized>(&self, c: &ReciprocalCircuit<C::Scalar>, gens: &BpppGens<C>, V: &[C::Compressed], transcript: &mut T) -> Result<(), ProofError> {
        verify(&self.0, c, gens, V, transcript)
    }

    /// The proof bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    /// Parse a proof for the circuit `c`.
    pub fn from_bytes(bytes: &[u8], c: &ReciprocalCircuit<C::Scalar>) -> Result<Self, ProofError> {
        proof_from_bytes(bytes, c).map(ReciprocalProof)
    }
}

/// The values committed after `alpha` (spec §4.3, two-phase prover): `w_R`, and the elements
/// of `w_O` in slot `LinR`, in `w_O` order.
#[derive(Clone)]
pub struct LateWitness<F: Field> {
    /// Right inputs of the ordinary multiplications.
    pub w_r: Vec<F>,
    /// The `LinR` elements of `w_O`, in `w_O` order.
    pub w_o_late: Vec<F>,
}

/// Prove `c` with the late values (`w_R` and the `LinR` elements of `w_O`) computed by `late`
/// from `alpha` and the reciprocals `w_P` (spec §4.3), for ordinary rows that read reciprocals.
/// The values of `w.w_r` and of the `LinR` elements of `w.w_o` are ignored (the lengths are
/// checked as for [`prove`]). Same transcript, randomness and
/// proof as [`prove`] given the same values; an error of `late` is returned as is.
pub(crate) fn prove_two_phase<C, T, R, LF>(
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    w: &ReciprocalWitness<C::Scalar>,
    late: LF,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof<C>, ProofError>
where
    C: Curve,
    T: BpppTranscript + ?Sized,
    R: RngCore + CryptoRng,
    LF: FnOnce(C::Scalar, &[C::Scalar]) -> Result<LateWitness<C::Scalar>, ProofError>,
{
    prove_with(c, gens, V, w, late, transcript, |t, d| rekeyed(t, c, d, w, rng), true)
}

/// The prover: `late` gives the values committed after `alpha`, `rng_for(transcript, digest)`
/// the randomness once the statement is absorbed.
#[allow(clippy::too_many_arguments)]
fn prove_with<C, T, R, LF, G>(
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    w: &ReciprocalWitness<C::Scalar>,
    late: LF,
    transcript: &mut T,
    rng_for: G,
    require_satisfied: bool,
) -> Result<CircuitProof<C>, ProofError>
where
    C: Curve,
    T: BpppTranscript + ?Sized,
    R: RngCore + CryptoRng,
    LF: FnOnce(C::Scalar, &[C::Scalar]) -> Result<LateWitness<C::Scalar>, ProofError>,
    G: FnOnce(&T, &[u8; 32]) -> R,
{
    check_gens(c, gens)?;
    c.check()?;
    c.check_witness(w)?;
    if V.len() != c.k {
        return Err(ProofError::FormatError);
    }
    let digest = absorb_statement(transcript, c, gens, V);
    let rng = &mut rng_for(&*transcript, &digest);
    let o = circuit::commit_o(gens, c.n_lin, c.n_mm(), &c.partition, &w.w_o, rng);
    let v2 = c.uses_eta();
    let (eta, w) = if v2 {
        transcript.append_point(b"C_O", &o.C_O);
        let eta: C::Scalar = transcript.challenge(b"eta");
        (eta, c.at_eta(w, eta))
    } else {
        (C::Scalar::ZERO, alloc::borrow::Cow::Borrowed(w))
    };
    let w = &*w;
    let w_l: Vec<C::Scalar> = w.w_d.iter().chain(&w.w_l).copied().collect();
    let mut ol = circuit::commit_l(gens, o, &w_l, rng);
    transcript.append_point(b"C_L", &ol.C_L);
    if !v2 {
        transcript.append_point(b"C_O", &ol.o.C_O);
    }
    let alpha: C::Scalar = transcript.challenge(b"alpha");
    let w_p = c.reciprocals(w, alpha)?;
    let lw = late(alpha, &w_p)?;
    if lw.w_r.len() != c.n_m || lw.w_o_late.len() != c.n_late() {
        return Err(ProofError::FormatError);
    }
    let mut full = w.clone();
    full.w_r = lw.w_r;
    let mut late_values = lw.w_o_late.into_iter();
    for (x, (slot, _)) in full.w_o.iter_mut().zip(&c.partition) {
        if *slot == Slot::LinR {
            *x = late_values.next().unwrap_or(C::Scalar::ZERO);
        }
    }
    ol.set_late(&c.partition, &full.w_o);
    let compiled = c.compile(eta, alpha)?;
    let cw = c.compiled_witness(&full, w_p);
    let cr = circuit::commit_r(gens, &ol, &cw.w_r, rng);
    transcript.append_point(b"C_R", &cr.C_R);
    circuit::prove_inner(&compiled, gens, &cw, &ol, &cr, transcript, rng, require_satisfied)
}

/// Verify a reciprocal form proof (spec §4.3).
pub(crate) fn verify<C: Curve, T: BpppTranscript + ?Sized>(
    proof: &CircuitProof<C>,
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    transcript: &mut T,
) -> Result<(), ProofError> {
    terms(proof, c, gens, V, transcript)?.check(gens)
}

/// [`verify`] up to the multiscalar multiplication, for batch verification.
pub(crate) fn terms<C: Curve, T: BpppTranscript + ?Sized>(
    proof: &CircuitProof<C>,
    c: &ReciprocalCircuit<C::Scalar>,
    gens: &BpppGens<C>,
    V: &[C::Compressed],
    transcript: &mut T,
) -> Result<circuit::Terms<C>, ProofError> {
    check_gens(c, gens)?;
    c.check().map_err(|_| ProofError::VerificationError)?;
    if V.len() != c.k {
        return Err(ProofError::VerificationError);
    }
    absorb_statement(transcript, c, gens, V);
    let eta = if c.uses_eta() {
        transcript.append_point(b"C_O", &proof.C_O);
        let eta: C::Scalar = transcript.challenge(b"eta");
        transcript.append_point(b"C_L", &proof.C_L);
        eta
    } else {
        transcript.append_point(b"C_L", &proof.C_L);
        transcript.append_point(b"C_O", &proof.C_O);
        C::Scalar::ZERO
    };
    let alpha: C::Scalar = transcript.challenge(b"alpha");
    let compiled = c.compile(eta, alpha)?;
    transcript.append_point(b"C_R", &proof.C_R);
    proof.inner_terms(&compiled, V, transcript)
}

/// Parse a proof for the reciprocal circuit `c` (spec §4.6).
pub(crate) fn proof_from_bytes<C: Curve>(bytes: &[u8], c: &ReciprocalCircuit<C::Scalar>) -> Result<CircuitProof<C>, ProofError> {
    CircuitProof::from_bytes_dims(bytes, c.n_lin, c.n_p.checked_add(c.n_m).ok_or(ProofError::FormatError)?)
}

#[cfg(test)]
#[path = "reciprocal_tests.rs"]
mod tests;

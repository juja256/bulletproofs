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

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};

use super::circuit::{self, ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
use super::gens::BpppGens;
use super::sparse::{BufHasher, SparseMatrix};
use super::transcript::BpppTranscript;
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// A public pole (spec §4.1): a polynomial in the challenge `eta`, `t(eta) = sum_e t_e eta^e`;
/// a circuit needs at least one coefficient (`check` rejects an empty one), and one coefficient
/// is a constant pole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pole(pub Vec<Scalar>);

impl From<Scalar> for Pole {
    fn from(t: Scalar) -> Self {
        Pole(vec![t])
    }
}

impl Pole {
    /// `t(eta)` (Horner).
    pub fn eval(&self, eta: Scalar) -> Scalar {
        self.0.iter().rev().fold(Scalar::ZERO, |acc, t| acc * eta + t)
    }
}

/// A reciprocal row (spec §4.1): `sum c * w'[col] / (X + t)` over the terms (no pole: `c *
/// w'[col]`) plus `sum c / (X + t)` over the constants (no pole: `c`), which must vanish.
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalRow {
    /// `(column of w', coefficient, pole)`.
    pub terms: Vec<(usize, Scalar, Option<Pole>)>,
    /// `(coefficient, pole)`.
    pub consts: Vec<(Scalar, Option<Pole>)>,
}

/// A component of a tuple pole: `sum c * w'[col] + constant` over early columns (`w_O` in
/// slots `NormO`, `LinO`).
#[derive(Clone, Debug, PartialEq)]
pub struct Component {
    /// `(column of w', coefficient)`.
    pub terms: Vec<(usize, Scalar)>,
    /// The constant.
    pub constant: Scalar,
}

/// A tuple pole (spec §4.1): `w_D,pole = sum_j eta^j x_j`, computed by the prover after `eta`
/// (the witness's value for it is ignored).
#[derive(Clone, Debug, PartialEq)]
pub struct TuplePole {
    /// The pole, `< n_p`.
    pub pole: usize,
    /// The components `x_0, x_1, ...` (at least one).
    pub components: Vec<Component>,
}

/// A reciprocal form circuit (spec §4.1). Columns index
/// `w' = w_D || w_L || w_P || w_R || w_O`.
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalCircuit {
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
    pub w_n: SparseMatrix,
    /// Affine term of the numerators.
    pub a_n: Vec<Scalar>,
    /// Ordinary multiplicative constraints, `n_m` rows.
    pub w_m: SparseMatrix,
    /// Affine term of the ordinary multiplicative constraints.
    pub a_m: Vec<Scalar>,
    /// Ordinary linear constraints.
    pub w_l: SparseMatrix,
    /// Affine term of the ordinary linear constraints.
    pub a_l: Vec<Scalar>,
    /// Reciprocal rows.
    pub recip: Vec<ReciprocalRow>,
    /// Tuple poles, in increasing pole order (spec §4.1); empty for a circuit of the paper.
    pub tuples: Vec<TuplePole>,
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
pub struct ReciprocalWitness {
    /// The poles.
    pub w_d: Vec<Scalar>,
    /// Left inputs of the ordinary multiplications.
    pub w_l: Vec<Scalar>,
    /// Right inputs of the ordinary multiplications.
    pub w_r: Vec<Scalar>,
    /// Further witness elements.
    pub w_o: Vec<Scalar>,
    /// The input vectors.
    pub v: Vec<Vec<Scalar>>,
    /// Blindings of the input commitments.
    pub s: Vec<Scalar>,
}

impl ReciprocalWitness {
    /// Overwrite every value with zero (the secrets of a prover that is done with them).
    pub(crate) fn clear(&mut self) {
        use clear_on_drop::clear::Clear;
        for x in self.w_d.iter_mut().chain(&mut self.w_l).chain(&mut self.w_r).chain(&mut self.w_o).chain(&mut self.s) {
            x.clear();
        }
        self.v.iter_mut().flatten().for_each(Clear::clear);
    }
}

impl core::fmt::Debug for ReciprocalWitness {
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

impl ReciprocalCircuit {
    fn n_mm(&self) -> usize {
        self.n_p + self.n_m
    }

    /// The generators of this circuit ([`BpppGens::new`] with `n_lin` and `n_p + n_m`).
    pub fn gens<'a>(&self, pc: &PedersenGens, bp: &'a BulletproofGens) -> Result<BpppGens<'a>, ProofError> {
        BpppGens::new(pc, bp, self.n_lin, self.n_p.checked_add(self.n_m).ok_or(ProofError::InvalidGeneratorsLength)?)
    }

    /// The `BulletproofGens` capacity [`ReciprocalCircuit::gens`] needs.
    pub fn gens_capacity(&self) -> usize {
        BpppGens::capacity(self.n_lin, self.n_p.saturating_add(self.n_m))
    }

    /// Whether the circuit uses the challenge `eta` (spec §4.1): a tuple pole, or a public pole
    /// with two or more coefficients. Only then is it proven with protocol v2.
    pub fn uses_eta(&self) -> bool {
        let long = |p: &Option<Pole>| p.as_ref().map_or(false, |p| p.0.len() > 1);
        !self.tuples.is_empty()
            || self.recip.iter().any(|r| r.terms.iter().any(|t| long(&t.2)) || r.consts.iter().any(|t| long(&t.1)))
    }

    /// Whether column `c` is early (committed in `C_O`: `w_O` in slots `NormO`, `LinO`).
    fn is_early(&self, c: usize) -> bool {
        let n_mm = self.n_mm();
        c >= 2 * n_mm && matches!(self.partition.get(c - 2 * n_mm), Some((Slot::NormO, _)) | Some((Slot::LinO, _)))
    }

    /// `w_D` with the tuple poles set for `eta` (spec §4.3); the components read `w_O` only.
    fn poles_at(&self, w: &ReciprocalWitness, eta: Scalar) -> Vec<Scalar> {
        let mut w_d = w.w_d.clone();
        let base = 2 * self.n_mm();
        for tp in &self.tuples {
            let mut acc = Scalar::ZERO;
            for x in tp.components.iter().rev() {
                let v: Scalar = x.terms.iter().map(|(c, k)| k * w.w_o[c - base]).sum::<Scalar>() + x.constant;
                acc = acc * eta + v;
            }
            w_d[tp.pole] = acc;
        }
        w_d
    }

    /// The witness with the tuple poles set for `eta` (a copy only if there are tuple poles).
    fn at_eta<'w>(&self, w: &'w ReciprocalWitness, eta: Scalar) -> alloc::borrow::Cow<'w, ReciprocalWitness> {
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
        self.compile_with(|t: &[Scalar]| Some(vec![Scalar::ONE; t.len()]), Scalar::ONE, Scalar::ONE)?.check()
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
        let empty = |p: &Option<Pole>| p.as_ref().map_or(false, |p| p.0.is_empty());
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
        let long = |p: &Option<Pole>| p.as_ref().map_or(false, |p| p.0.len() > 1);
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
    fn compile_with<F: FnOnce(&[Scalar]) -> Option<Vec<Scalar>>>(&self, coef: F, alpha: Scalar, eta: Scalar) -> Result<ArithmeticCircuit, ProofError> {
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
        let pows: Vec<Scalar> = core::iter::successors(Some(Scalar::ONE), |e| Some(e * eta)).take(m_max).collect();
        const CHUNK: usize = 4096;
        let n_t = self.tuples.len();
        let build = |k: usize| {
            let mut m = SparseMatrix::new(n_w);
            let mut a: Vec<Scalar> = Vec::with_capacity(CHUNK);
            for tp in &self.tuples[k * CHUNK..((k + 1) * CHUNK).min(n_t)] {
                let components = || tp.components.iter().zip(&pows);
                m.push_row(core::iter::once((tp.pole, Scalar::ONE)).chain(components().flat_map(|(x, e)| x.terms.iter().map(move |(c, v)| (*c, -e * v)))));
                a.push(components().map(|(x, e)| -(e * x.constant)).sum());
            }
            (m, a)
        };
        crate::util::map_in_order((n_t + CHUNK - 1) / CHUNK, build, |(m, a)| {
            w_l.extend_rows(&m);
            a_l.extend(a);
        });
        // the factors of all terms with a pole, in row order (terms, then constants), at once
        let poles = || self.recip.iter().flat_map(|row| row.terms.iter().map(|(_, _, p)| p).chain(row.consts.iter().map(|(_, p)| p)));
        let values: Vec<Scalar> = poles().flatten().map(|t| t.eval(eta)).collect();
        let factors = coef(&values).ok_or(ProofError::VerificationError)?;
        debug_assert_eq!(factors.len(), values.len());
        drop(values);
        let mut factors = factors.into_iter();
        let mut factor = |pole: &Option<Pole>| pole.as_ref().map_or(Scalar::ONE, |_| factors.next().expect("one factor per pole"));
        for row in &self.recip {
            let terms: Vec<(usize, Scalar)> = row.terms.iter().map(|(c, v, pole)| (*c, v * factor(pole))).collect();
            w_l.push_row(terms);
            let a = row.consts.iter().map(|(v, pole)| v * factor(pole)).sum();
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
    fn compile(&self, eta: Scalar, alpha: Scalar) -> Result<ArithmeticCircuit, ProofError> {
        // 1 / (alpha + t) for every pole value t, by one batch inversion (public values)
        let inverses = |t: &[Scalar]| {
            let mut d: Vec<Scalar> = t.iter().map(|t| alpha + t).collect();
            if d.iter().any(|d| *d == Scalar::ZERO) {
                return None;
            }
            Scalar::batch_invert(&mut d);
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
            h.update(a.as_bytes());
        }
        let pole = |h: &mut BufHasher, p: &Option<Pole>| match p {
            None => h.update([0u8]),
            Some(t) => {
                h.update([1u8]);
                if v2 {
                    h.update((t.0.len() as u64).to_le_bytes());
                    t.0.iter().for_each(|x| h.update(x.as_bytes()));
                } else {
                    t.0.iter().for_each(|x| h.update(x.as_bytes())); // one coefficient
                }
            }
        };
        for row in &self.recip {
            h.update((row.terms.len() as u64).to_le_bytes());
            for (c, v, p) in &row.terms {
                h.update((*c as u64).to_le_bytes());
                h.update(v.as_bytes());
                pole(&mut h, p);
            }
            h.update((row.consts.len() as u64).to_le_bytes());
            for (v, p) in &row.consts {
                h.update(v.as_bytes());
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
                    h.update(v.as_bytes());
                }
                h.update(x.constant.as_bytes());
            }
        }
        h.finalize()
    }

    fn check_witness(&self, w: &ReciprocalWitness) -> Result<(), ProofError> {
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
    fn full(&self, w: &ReciprocalWitness, w_p: &[Scalar]) -> Vec<Scalar> {
        w.w_d.iter().chain(&w.w_l).chain(w_p).chain(&w.w_r).chain(&w.w_o).copied().collect()
    }

    /// The numerators `(W_n w' + f_m w_V + a_n)_i` (initial columns only, so `w_P` is not needed).
    fn numerators(&self, w: &ReciprocalWitness) -> Vec<Scalar> {
        let full = self.full(w, &vec![Scalar::ZERO; self.n_p]);
        let w_v: Vec<Scalar> = w.v.iter().flatten().copied().collect();
        let f_m = if self.f_m { Scalar::ONE } else { Scalar::ZERO };
        self.w_n
            .mul_vec(&full)
            .iter()
            .zip(&self.a_n)
            .enumerate()
            .map(|(i, (x, a))| x + a + f_m * w_v.get(i).copied().unwrap_or(Scalar::ZERO))
            .collect()
    }

    /// Whether `w` satisfies the circuit for the challenges `eta` (ignored by a circuit that
    /// does not use it) and `alpha` (spec §4.1): with the tuple poles set for `eta`, every
    /// reciprocal row vanishes as a rational function of `X` (all multiplicities per pole value
    /// and the polynomial part are zero), and the compiled circuit holds (for rows that read
    /// reciprocals).
    pub fn is_satisfied(&self, w: &ReciprocalWitness, eta: Scalar, alpha: Scalar) -> bool {
        if self.check().is_err() || self.check_witness(w).is_err() {
            return false;
        }
        let w = &*self.at_eta(w, eta);
        let num = self.numerators(w);
        let full = self.full(w, &vec![Scalar::ZERO; self.n_p]);
        for row in &self.recip {
            let mut poles: Vec<(Scalar, Scalar)> = Vec::new();
            let mut poly = Scalar::ZERO;
            let mut add = |pole: Option<Scalar>, x: Scalar| match pole {
                None => poly += x,
                Some(t) => match poles.iter_mut().find(|(p, _)| *p == t) {
                    Some((_, m)) => *m += x,
                    None => poles.push((t, x)),
                },
            };
            for (c, v, pole) in &row.terms {
                match self.col(*c) {
                    Col::Reciprocal(i) => add(Some(w.w_d[i]), v * num[i]),
                    _ => add(pole.as_ref().map(|p| p.eval(eta)), v * full[*c]),
                }
            }
            for (v, pole) in &row.consts {
                add(pole.as_ref().map(|p| p.eval(eta)), *v);
            }
            if poly != Scalar::ZERO || poles.iter().any(|(_, m)| *m != Scalar::ZERO) {
                return false;
            }
        }
        match (self.reciprocals(w, alpha), self.compile(eta, alpha)) {
            (Ok(w_p), Ok(c)) => c.is_satisfied(&self.compiled_witness(w, w_p)),
            _ => false,
        }
    }

    /// `w_P,i = num_i / (alpha + w_D,i)`; an error if a denominator is zero.
    fn reciprocals(&self, w: &ReciprocalWitness, alpha: Scalar) -> Result<Vec<Scalar>, ProofError> {
        use clear_on_drop::clear::Clear;
        use subtle::ConstantTimeEq;
        // One inversion for all denominators (Montgomery's trick, constant time); a zero
        // denominator would spoil the whole batch, so it is checked first.
        let mut inv: Vec<Scalar> = w.w_d.iter().map(|d| alpha + d).collect();
        let any_zero = inv.iter().fold(subtle::Choice::from(0u8), |acc, d| acc | d.ct_eq(&Scalar::ZERO));
        if bool::from(any_zero) {
            inv.iter_mut().for_each(Clear::clear);
            return Err(ProofError::VerificationError);
        }
        Scalar::batch_invert(&mut inv);
        let out = self.numerators(w).iter().zip(&inv).map(|(n, i)| n * i).collect();
        inv.iter_mut().for_each(Clear::clear);
        Ok(out)
    }

    /// The compiled circuit and witness for `(eta, alpha)` (tests).
    #[cfg(test)]
    pub(crate) fn compiled_for_test(&self, w: &ReciprocalWitness, eta: Scalar, alpha: Scalar) -> (ArithmeticCircuit, CircuitWitness) {
        let w = &*self.at_eta(w, eta);
        let w_p = self.reciprocals(w, alpha).unwrap();
        (self.compile(eta, alpha).unwrap(), self.compiled_witness(w, w_p))
    }

    #[cfg(test)]
    pub(crate) fn reciprocals_for_test(&self, w: &ReciprocalWitness, eta: Scalar, alpha: Scalar) -> Vec<Scalar> {
        self.reciprocals(&self.at_eta(w, eta), alpha).unwrap()
    }

    /// `w_D` with the tuple poles set for `eta` (tests).
    #[cfg(test)]
    pub(crate) fn poles_for_test(&self, w: &ReciprocalWitness, eta: Scalar) -> Vec<Scalar> {
        self.poles_at(w, eta)
    }

    /// The late values given in the witness itself (the one-phase prover).
    fn given_late(&self, w: &ReciprocalWitness) -> LateWitness {
        LateWitness { w_r: w.w_r.clone(), w_o_late: self.late_elements(&w.w_o) }
    }

    /// The number of `LinR` slots (elements of `w_O` committed after `alpha`).
    fn n_late(&self) -> usize {
        self.partition.iter().filter(|(s, _)| *s == Slot::LinR).count()
    }

    /// The `LinR` elements of `w_o`, in order.
    fn late_elements(&self, w_o: &[Scalar]) -> Vec<Scalar> {
        w_o.iter().zip(&self.partition).filter(|(_, (s, _))| *s == Slot::LinR).map(|(x, _)| *x).collect()
    }

    fn compiled_witness(&self, w: &ReciprocalWitness, w_p: Vec<Scalar>) -> CircuitWitness {
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
fn absorb_statement<T: BpppTranscript>(t: &mut T, c: &ReciprocalCircuit, gens: &BpppGens, V: &[CompressedRistretto]) -> [u8; 32] {
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

fn check_gens(c: &ReciprocalCircuit, gens: &BpppGens) -> Result<(), ProofError> {
    gens.check_dims(c.n_lin, c.n_p.checked_add(c.n_m).ok_or(ProofError::InvalidGeneratorsLength)?)
}

/// Prove that `w` satisfies the reciprocal form circuit `c` for the input commitments `V`
/// (spec §4.3). Generators: [`BpppGens::new`] with `n_lin` and `n_p + n_m`. Returns an error if
/// `alpha + w_D,i = 0` (probability `n_p / 2^252`) or the witness does not satisfy `c`.
pub(crate) fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    prove_checked(c, gens, V, w, transcript, rng, true)
}

/// [`prove`]; with `require_satisfied = false` an unsatisfied witness is proven instead of
/// refused (feature `cheats` of the R1CS front end: such a proof must not verify).
pub(crate) fn prove_checked<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError> {
    prove_with(c, gens, V, w, |_, _| Ok(c.given_late(w)), transcript, |t, d| rekeyed(t, c, d, w, rng), require_satisfied)
}

/// The prover's RNG from the transcript, the digest and the initial witness (spec §1; the late
/// values are not known to the two-phase prover before `alpha`, and both provers must agree).
fn rekeyed<T: BpppTranscript, R: RngCore + CryptoRng>(t: &T, c: &ReciprocalCircuit, digest: &[u8; 32], w: &ReciprocalWitness, rng: &mut R) -> merlin::TranscriptRng {
    let early_o = w.w_o.iter().zip(&c.partition).filter(|(_, (s, _))| *s != Slot::LinR).map(|(x, _)| x);
    // tuple poles are not known before eta: hashed as 0 (spec §1)
    let mut w_d = w.w_d.clone();
    c.tuples.iter().for_each(|tp| w_d[tp.pole] = Scalar::ZERO);
    let secrets = w_d.iter().chain(&w.w_l).chain(early_o).chain(w.v.iter().flatten()).chain(&w.s);
    let r = super::transcript::prover_rng(t, b"reciprocal", digest, secrets, rng);
    w_d.iter_mut().for_each(clear_on_drop::clear::Clear::clear);
    r
}

/// The prover with the caller's RNG as is (the reference vectors replay its values), and an
/// unsatisfied witness proven unless `require_satisfied` (tests).
#[cfg(test)]
pub(crate) fn prove_impl<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError> {
    prove_with(c, gens, V, w, |_, _| Ok(c.given_late(w)), transcript, |_, _| rng, require_satisfied)
}

/// A proof for a reciprocal form circuit (spec §4); the encoding is that of a
/// [`CircuitProof`] for the compiled circuit (spec §4.6).
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalProof(pub(crate) CircuitProof);

impl ReciprocalProof {
    /// Prove that `w` satisfies `c` for the input commitments `V` (spec §4.3). Generators:
    /// [`ReciprocalCircuit::gens`]. An error if `alpha + w_D,i = 0` (probability
    /// `n_p / 2^252`) or if the witness does not satisfy `c`.
    pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
        c: &ReciprocalCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        w: &ReciprocalWitness,
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<Self, ProofError> {
        prove(c, gens, V, w, transcript, rng).map(ReciprocalProof)
    }

    /// [`ReciprocalProof::prove`] with the late values (`w_R` and the `LinR` elements of `w_O`)
    /// computed by `late` from `alpha` and the reciprocals `w_P` (spec §4.3), for ordinary rows
    /// that read reciprocals; the late entries of `w` are ignored. Same transcript, randomness
    /// and proof as `prove` given the same values; an error of `late` is returned as is.
    pub fn prove_two_phase<T, R, F>(
        c: &ReciprocalCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        w: &ReciprocalWitness,
        late: F,
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<Self, ProofError>
    where
        T: BpppTranscript,
        R: RngCore + CryptoRng,
        F: FnOnce(Scalar, &[Scalar]) -> Result<LateWitness, ProofError>,
    {
        prove_two_phase(c, gens, V, w, late, transcript, rng).map(ReciprocalProof)
    }

    /// Verify for the circuit `c` and the input commitments `V`.
    pub fn verify<T: BpppTranscript>(&self, c: &ReciprocalCircuit, gens: &BpppGens, V: &[CompressedRistretto], transcript: &mut T) -> Result<(), ProofError> {
        verify(&self.0, c, gens, V, transcript)
    }

    /// The proof bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    /// Parse a proof for the circuit `c`.
    pub fn from_bytes(bytes: &[u8], c: &ReciprocalCircuit) -> Result<Self, ProofError> {
        proof_from_bytes(bytes, c).map(ReciprocalProof)
    }
}

/// The values committed after `alpha` (spec §4.3, two-phase prover): `w_R`, and the elements
/// of `w_O` in slot `LinR`, in `w_O` order.
#[derive(Clone)]
pub struct LateWitness {
    /// Right inputs of the ordinary multiplications.
    pub w_r: Vec<Scalar>,
    /// The `LinR` elements of `w_O`, in `w_O` order.
    pub w_o_late: Vec<Scalar>,
}

/// Prove `c` with the late values (`w_R` and the `LinR` elements of `w_O`) computed by `late`
/// from `alpha` and the reciprocals `w_P` (spec §4.3), for ordinary rows that read reciprocals.
/// The values of `w.w_r` and of the `LinR` elements of `w.w_o` are ignored (the lengths are
/// checked as for [`prove`]). Same transcript, randomness and
/// proof as [`prove`] given the same values; an error of `late` is returned as is.
pub(crate) fn prove_two_phase<T, R, F>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    late: F,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError>
where
    T: BpppTranscript,
    R: RngCore + CryptoRng,
    F: FnOnce(Scalar, &[Scalar]) -> Result<LateWitness, ProofError>,
{
    prove_with(c, gens, V, w, late, transcript, |t, d| rekeyed(t, c, d, w, rng), true)
}

/// The prover: `late` gives the values committed after `alpha`, `rng_for(transcript, digest)`
/// the randomness once the statement is absorbed.
#[allow(clippy::too_many_arguments)]
fn prove_with<T, R, F, G>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    late: F,
    transcript: &mut T,
    rng_for: G,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError>
where
    T: BpppTranscript,
    R: RngCore + CryptoRng,
    F: FnOnce(Scalar, &[Scalar]) -> Result<LateWitness, ProofError>,
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
        let eta = transcript.challenge(b"eta");
        (eta, c.at_eta(w, eta))
    } else {
        (Scalar::ZERO, alloc::borrow::Cow::Borrowed(w))
    };
    let w = &*w;
    let w_l: Vec<Scalar> = w.w_d.iter().chain(&w.w_l).copied().collect();
    let mut ol = circuit::commit_l(gens, o, &w_l, rng);
    transcript.append_point(b"C_L", &ol.C_L);
    if !v2 {
        transcript.append_point(b"C_O", &ol.o.C_O);
    }
    let alpha = transcript.challenge(b"alpha");
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
            *x = late_values.next().unwrap_or(Scalar::ZERO);
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
pub(crate) fn verify<T: BpppTranscript>(
    proof: &CircuitProof,
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    transcript: &mut T,
) -> Result<(), ProofError> {
    terms(proof, c, gens, V, transcript)?.check(gens)
}

/// [`verify`] up to the multiscalar multiplication, for batch verification.
pub(crate) fn terms<T: BpppTranscript>(
    proof: &CircuitProof,
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    transcript: &mut T,
) -> Result<circuit::Terms, ProofError> {
    check_gens(c, gens)?;
    c.check().map_err(|_| ProofError::VerificationError)?;
    if V.len() != c.k {
        return Err(ProofError::VerificationError);
    }
    absorb_statement(transcript, c, gens, V);
    let eta = if c.uses_eta() {
        transcript.append_point(b"C_O", &proof.C_O);
        let eta = transcript.challenge(b"eta");
        transcript.append_point(b"C_L", &proof.C_L);
        eta
    } else {
        transcript.append_point(b"C_L", &proof.C_L);
        transcript.append_point(b"C_O", &proof.C_O);
        Scalar::ZERO
    };
    let alpha = transcript.challenge(b"alpha");
    let compiled = c.compile(eta, alpha)?;
    transcript.append_point(b"C_R", &proof.C_R);
    proof.inner_terms(&compiled, V, transcript)
}

/// Parse a proof for the reciprocal circuit `c` (spec §4.6).
pub(crate) fn proof_from_bytes(bytes: &[u8], c: &ReciprocalCircuit) -> Result<CircuitProof, ProofError> {
    CircuitProof::from_bytes_dims(bytes, c.n_lin, c.n_p.checked_add(c.n_m).ok_or(ProofError::FormatError)?)
}

#[cfg(test)]
#[path = "reciprocal_tests.rs"]
mod tests;

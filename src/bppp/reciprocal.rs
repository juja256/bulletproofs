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
use sha3::{Digest, Sha3_256};

use super::circuit::{self, ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
use super::gens::BpppGens;
use super::sparse::SparseMatrix;
use super::transcript::{BpppTranscript, DynRng, Randomness};
use crate::errors::ProofError;

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
        self.compile_with(|_| Some(Scalar::ONE), Scalar::ONE, Scalar::ONE)?.check()
    }

    /// The compiled circuit, with `coef(t)` the factor of a term with a pole of value `t`
    /// (`None` when undefined), `alpha` the coefficient subtracted at the reciprocal columns,
    /// and `eta` the challenge of the tuple poles and pole polynomials.
    fn compile_with<F: Fn(Scalar) -> Option<Scalar>>(&self, coef: F, alpha: Scalar, eta: Scalar) -> Result<ArithmeticCircuit, ProofError> {
        let n_mm = self.n_mm();
        let n_w = 2 * n_mm + self.n_o;
        let mut w_m = SparseMatrix::new(n_w);
        for i in 0..self.n_p {
            w_m.push_row(self.w_n.row(i).map(|(c, v)| (c, *v)).chain(Some((n_mm + i, -alpha))));
        }
        for r in 0..self.n_m {
            w_m.push_row(self.w_m.row(r).map(|(c, v)| (c, *v)));
        }
        let mut w_l = SparseMatrix::new(n_w);
        for r in 0..self.w_l.n_rows() {
            w_l.push_row(self.w_l.row(r).map(|(c, v)| (c, *v)));
        }
        let mut a_l = self.a_l.clone();
        // w_D,i - sum_j eta^j x_ij = 0
        for tp in &self.tuples {
            let mut terms = vec![(tp.pole, Scalar::ONE)];
            let mut a = Scalar::ZERO;
            let mut e = Scalar::ONE;
            for x in &tp.components {
                terms.extend(x.terms.iter().map(|(c, v)| (*c, -e * v)));
                a -= e * x.constant;
                e *= eta;
            }
            w_l.push_row(terms);
            a_l.push(a);
        }
        let factor = |pole: &Option<Pole>| match pole {
            None => Ok(Scalar::ONE),
            Some(t) => coef(t.eval(eta)).ok_or(ProofError::VerificationError),
        };
        for row in &self.recip {
            let mut terms = Vec::with_capacity(row.terms.len());
            for (c, v, pole) in &row.terms {
                terms.push((*c, v * factor(pole)?));
            }
            w_l.push_row(terms);
            let mut a = Scalar::ZERO;
            for (v, pole) in &row.consts {
                a += v * factor(pole)?;
            }
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
        self.compile_with(
            |t| {
                let d = alpha + t;
                if d == Scalar::ZERO {
                    None
                } else {
                    Some(d.invert())
                }
            },
            alpha,
            eta,
        )
    }

    /// The reciprocal circuit digest (spec §4.4).
    pub fn digest(&self) -> [u8; 32] {
        let v2 = self.uses_eta();
        let mut h = Sha3_256::new();
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
        let pole = |h: &mut Sha3_256, p: &Option<Pole>| match p {
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
        h.finalize().into()
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
        self.numerators(w)
            .iter()
            .zip(&w.w_d)
            .map(|(n, d)| {
                let den = alpha + d;
                if den == Scalar::ZERO {
                    Err(ProofError::VerificationError)
                } else {
                    Ok(n * den.invert())
                }
            })
            .collect()
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

fn absorb_statement<T: BpppTranscript>(t: &mut T, c: &ReciprocalCircuit, gens: &BpppGens, V: &[CompressedRistretto]) {
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
    t.append_point(b"G", &gens.g.compress());
    t.append_point(b"H_0", &gens.h[0].compress());
    t.append_message(b"circuit", &c.digest());
    for v in V {
        t.append_point(b"V", v);
    }
}

fn check_gens(c: &ReciprocalCircuit, gens: &BpppGens) -> Result<(), ProofError> {
    let n_mm = c.n_p.checked_add(c.n_m);
    if c.n_lin.checked_add(7) != Some(gens.h.len()) || n_mm != Some(gens.n.len()) {
        return Err(ProofError::InvalidGeneratorsLength);
    }
    Ok(())
}

/// Prove that `w` satisfies the reciprocal form circuit `c` for the input commitments `V`
/// (spec §4.3). Generators: [`BpppGens::new`] with `n_lin` and `n_p + n_m`. Returns an error if
/// `alpha + w_D,i = 0` (probability `n_p / 2^252`) or the witness does not satisfy `c`.
pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    let fixed = |_: Scalar, _: &[Scalar]| Ok(LateWitness { w_r: w.w_r.clone(), w_o_late: c.late_elements(&w.w_o) });
    prove_with(c, gens, V, w, fixed, transcript, Randomness::Derived(rng), true)
}

/// [`prove`] without the refusal of an unsatisfied witness (feature `cheats`: the proof must
/// not verify).
#[cfg(feature = "cheats")]
pub(crate) fn prove_unsatisfied<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    let fixed = |_: Scalar, _: &[Scalar]| Ok(LateWitness { w_r: w.w_r.clone(), w_o_late: c.late_elements(&w.w_o) });
    prove_with(c, gens, V, w, fixed, transcript, Randomness::Derived(rng), false)
}

#[cfg(not(feature = "cheats"))]
pub(crate) fn prove_unsatisfied<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    prove(c, gens, V, w, transcript, rng)
}

/// The prover's RNG from the transcript, the digest and the initial witness (spec §1; the late
/// values are not known to the two-phase prover before `alpha`, and both provers must agree).
fn rekeyed<T: BpppTranscript, R: RngCore + CryptoRng>(t: &T, c: &ReciprocalCircuit, w: &ReciprocalWitness, rng: &mut R) -> merlin::TranscriptRng {
    let early_o = w.w_o.iter().zip(&c.partition).filter(|(_, (s, _))| *s != Slot::LinR).map(|(x, _)| x);
    // tuple poles are not known before eta: hashed as 0 (spec §1)
    let mut w_d = w.w_d.clone();
    c.tuples.iter().for_each(|tp| w_d[tp.pole] = Scalar::ZERO);
    let secrets = w_d.iter().chain(&w.w_l).chain(early_o).chain(w.v.iter().flatten()).chain(&w.s);
    let r = super::transcript::prover_rng(t, b"reciprocal", &c.digest(), secrets, rng);
    w_d.iter_mut().for_each(clear_on_drop::clear::Clear::clear);
    r
}

pub(crate) fn prove_impl<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError> {
    let fixed = |_: Scalar, _: &[Scalar]| {
        Ok(LateWitness { w_r: w.w_r.clone(), w_o_late: c.late_elements(&w.w_o) })
    };
    prove_with(c, gens, V, w, fixed, transcript, Randomness::Given(rng), require_satisfied)
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
pub fn prove_two_phase<T, R, F>(
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
    prove_with(c, gens, V, w, late, transcript, Randomness::Derived(rng), true)
}

#[allow(clippy::too_many_arguments)]
fn prove_with<T, R, F>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    late: F,
    transcript: &mut T,
    randomness: Randomness<R>,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError>
where
    T: BpppTranscript,
    R: RngCore + CryptoRng,
    F: FnOnce(Scalar, &[Scalar]) -> Result<LateWitness, ProofError>,
{
    check_gens(c, gens)?;
    c.check()?;
    c.check_witness(w)?;
    if V.len() != c.k {
        return Err(ProofError::FormatError);
    }
    absorb_statement(transcript, c, gens, V);
    let mut derived;
    let rng: &mut dyn rand_core::CryptoRngCore = match randomness {
        Randomness::Given(r) => r,
        Randomness::Derived(r) => {
            derived = rekeyed(&*transcript, c, w, r);
            &mut derived
        }
    };
    let rng = &mut DynRng(rng);
    let o = circuit::commit_o(gens, c.n_lin, c.n_mm(), &c.partition, &w.w_o, rng);
    let (eta, w) = if c.uses_eta() {
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
    if !c.uses_eta() {
        transcript.append_point(b"C_O", &ol.C_O);
    }
    let alpha = transcript.challenge(b"alpha");
    let w_p = c.reciprocals(w, alpha)?;
    let lw = late(alpha, &w_p)?;
    let n_late = c.partition.iter().filter(|(s, _)| *s == Slot::LinR).count();
    if lw.w_r.len() != c.n_m || lw.w_o_late.len() != n_late {
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
pub fn verify<T: BpppTranscript>(
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
    proof.inner_terms(&compiled, gens, V, transcript)
}

/// Parse a proof for the reciprocal circuit `c` (spec §4.6).
pub fn proof_from_bytes(bytes: &[u8], c: &ReciprocalCircuit) -> Result<CircuitProof, ProofError> {
    let shape = ArithmeticCircuit {
        n_m: c.n_p.checked_add(c.n_m).ok_or(ProofError::FormatError)?,
        n_o: c.n_o,
        n_v: c.n_v,
        n_lin: c.n_lin,
        k: c.k,
        w_l: SparseMatrix::new(0),
        a_l: vec![],
        w_m: SparseMatrix::new(0),
        a_m: vec![],
        f_l: c.f_l,
        f_m: c.f_m,
        partition: vec![],
    };
    CircuitProof::from_bytes(bytes, &shape)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bppp::transcript::Replay;
    use crate::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// A reciprocal range proof (paper §6.4) for `value` with `n_digits` digits in `base`:
    /// poles are the digits, numerators 1, one reciprocal row
    /// `sum_j 1/(X + d_j) - sum_s m_s/(X + s) = 0`, one linear row `sum_j base^j d_j = v`.
    /// Multiplicities sit in `LinL` slots (`shared`) or `NormO` slots (inline).
    fn range_proof(base: u64, n_digits: usize, digits: &[u64], shared: bool) -> (ReciprocalCircuit, ReciprocalWitness) {
        let b = base as usize;
        let n_p = n_digits;
        let n_m = if shared { 0 } else { b.saturating_sub(n_p) };
        let n_mm = n_p + n_m;
        let n_lin = if shared { b } else { 0 };
        let n_w = 2 * n_mm + b;
        let mut w_l = SparseMatrix::new(n_w);
        let mut pw = Scalar::ONE;
        let mut row = Vec::new();
        for j in 0..n_p {
            row.push((j, -pw));
            pw *= Scalar::from(base);
        }
        w_l.push_row(row);
        let mut w_n = SparseMatrix::new(n_w);
        for _ in 0..n_p {
            w_n.push_row(vec![]);
        }
        let mut w_m = SparseMatrix::new(n_w);
        for _ in 0..n_m {
            w_m.push_row(vec![]);
        }
        let terms = (0..n_p)
            .map(|j| (n_mm + j, Scalar::ONE, None))
            .chain((0..b).map(|s| (2 * n_mm + s, -Scalar::ONE, Some(Scalar::from(s as u64).into()))))
            .collect();
        let c = ReciprocalCircuit {
            n_p,
            n_m,
            n_o: b,
            n_v: 1,
            n_lin,
            k: 1,
            w_n,
            a_n: vec![Scalar::ONE; n_p],
            w_m,
            a_m: vec![Scalar::ZERO; n_m],
            w_l,
            a_l: vec![Scalar::ZERO],
            recip: vec![ReciprocalRow { terms, consts: vec![] }],
            tuples: vec![],
            f_l: true,
            f_m: false,
            partition: (0..b).map(|s| if shared { (Slot::LinL, s) } else { (Slot::NormO, s) }).collect(),
        };
        let mut m = vec![0u64; b];
        for &d in digits {
            if (d as usize) < b {
                m[d as usize] += 1;
            }
        }
        let value: Scalar = digits.iter().rev().fold(Scalar::ZERO, |acc, &d| acc * Scalar::from(base) + Scalar::from(d));
        let w = ReciprocalWitness {
            w_d: digits.iter().map(|&d| Scalar::from(d)).collect(),
            w_l: vec![Scalar::ZERO; n_m],
            w_r: vec![Scalar::ZERO; n_m],
            w_o: m.iter().map(|&x| Scalar::from(x)).collect(),
            v: vec![vec![value]],
            s: vec![Scalar::from(7u64)],
        };
        (c, w)
    }

    fn digits_of(mut v: u64, base: u64, n: usize) -> Vec<u64> {
        (0..n)
            .map(|_| {
                let d = v % base;
                v /= base;
                d
            })
            .collect()
    }

    fn setup(c: &ReciprocalCircuit) -> (PedersenGens, BulletproofGens) {
        (PedersenGens::default(), BulletproofGens::new((c.n_p + c.n_m).max(c.n_lin + 6), 1))
    }

    fn inputs(g: &BpppGens, w: &ReciprocalWitness) -> Vec<CompressedRistretto> {
        w.v.iter().zip(&w.s).map(|(v, s)| g.commit_input(v, *s).compress()).collect()
    }

    /// The prover reproduces the independent Python reference
    /// (`tests/vectors/bppp/reciprocal.json`): reciprocals, commitments, norm argument; the
    /// verifier accepts exactly the satisfied cases.
    #[test]
    fn matches_reference_vectors() {
        use crate::bppp::testutil;
        let file: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/bppp/reciprocal.json")).unwrap();
        let mut invalid = 0;
        for case in file["cases"].as_array().unwrap() {
            let c = testutil::recip_circuit(case);
            assert_eq!(c.w_l.n_rows(), case["n_l"].as_u64().unwrap() as usize);
            if case["shape_ok"].as_bool() == Some(false) {
                assert!(c.check().is_err(), "{}: shape", case["name"]);
                invalid += 1;
                continue;
            }
            c.check().unwrap_or_else(|e| panic!("{}: {:?}", case["name"], e));
            testutil::run_recip_case(case, &c, &testutil::recip_witness(case));
        }
        assert!(invalid >= 2, "shape-invalid v2 cases");
    }

    #[test]
    fn range_proofs_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(30);
        for &(base, n) in &[(2u64, 8usize), (4, 4), (16, 4), (16, 16)] {
            let max = if base.pow(n as u32 - 1) > u64::MAX / base { u64::MAX } else { base.pow(n as u32) - 1 };
            for &value in &[0u64, 1, max / 3, max] {
                for &shared in &[false, true] {
                    let (c, w) = range_proof(base, n, &digits_of(value, base, n), shared);
                    let (pc, bp) = setup(&c);
                    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
                    let V = inputs(&g, &w);
                    let proof = prove(&c, &g, &V, &w, &mut Transcript::new(b"rp"), &mut rng)
                        .unwrap_or_else(|e| panic!("base {} value {} shared {}: {:?}", base, value, shared, e));
                    let parsed = proof_from_bytes(&proof.to_bytes(), &c).unwrap();
                    assert_eq!(parsed, proof);
                    verify(&proof, &c, &g, &V, &mut Transcript::new(b"rp")).unwrap();
                    assert!(verify(&proof, &c, &g, &V, &mut Transcript::new(b"other")).is_err());
                }
            }
        }
    }

    /// A digit outside `[0, base)` has no public pole to cancel against: the prover refuses,
    /// and a proof made without that check does not verify.
    #[test]
    fn digit_out_of_range_is_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(31);
        for &shared in &[false, true] {
            let mut digits = digits_of(1000, 16, 4);
            digits[1] = 16; // value = 1000 + 16*16 - digit, still a valid linear relation
            let (c, w) = range_proof(16, 4, &digits, shared);
            assert!(!c.is_satisfied(&w, Scalar::ZERO, Scalar::from(12345u64)));
            let (pc, bp) = setup(&c);
            let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
            let V = inputs(&g, &w);
            assert!(prove(&c, &g, &V, &w, &mut Transcript::new(b"rp"), &mut rng).is_err());
            let proof = prove_impl(&c, &g, &V, &w, &mut Transcript::new(b"rp"), &mut rng, false).unwrap();
            assert!(verify(&proof, &c, &g, &V, &mut Transcript::new(b"rp")).is_err());
        }
    }

    /// The initial witness is committed before `alpha`, `C_R` after it; the verifier absorbs
    /// the same bytes.
    #[test]
    fn transcript_binds_initial_witness_before_alpha() {
        let mut rng = ChaCha20Rng::seed_from_u64(32);
        let (c, w) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        let (pc, bp) = setup(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let V = inputs(&g, &w);
        let chal: Vec<Scalar> = (5..40u64).map(Scalar::from).collect();
        let mut t = Replay::new(chal.clone());
        let proof = prove(&c, &g, &V, &w, &mut t, &mut rng).unwrap();
        let labels: Vec<&[u8]> = t.log.iter().map(|(l, _)| *l).collect();
        let pos = |l: &[u8]| labels.iter().position(|x| *x == l).unwrap();
        assert_eq!(labels[0], &b"bppp-reciprocal v1"[..]);
        assert!(pos(b"circuit") < pos(b"V") && pos(b"V") < pos(b"C_L"));
        assert!(pos(b"C_L") < pos(b"C_O") && pos(b"C_O") < pos(b"alpha") && pos(b"alpha") < pos(b"C_R"));
        assert!(pos(b"C_R") < pos(b"rho"));
        assert_eq!(t.log[pos(b"circuit")].1, c.digest().to_vec());
        assert_eq!(t.log[pos(b"C_L")].1, proof.C_L.as_bytes().to_vec());
        assert_eq!(t.log[pos(b"C_O")].1, proof.C_O.as_bytes().to_vec());
        assert_eq!(t.log[pos(b"C_R")].1, proof.C_R.as_bytes().to_vec());
        let mut tv = Replay::new(chal);
        verify(&proof, &c, &g, &V, &mut tv).unwrap();
        assert_eq!(tv.log, t.log);
    }

    /// `alpha = -w_D,i` makes a reciprocal undefined: the prover fails (paper §6.3).
    #[test]
    fn pole_at_alpha_fails() {
        let mut rng = ChaCha20Rng::seed_from_u64(33);
        let (c, w) = range_proof(4, 3, &digits_of(37, 4, 3), false);
        let (pc, bp) = setup(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let V = inputs(&g, &w);
        let mut chal: Vec<Scalar> = (5..40u64).map(Scalar::from).collect();
        chal[0] = -w.w_d[1];
        assert!(prove(&c, &g, &V, &w, &mut Replay::new(chal), &mut rng).is_err());
    }

    /// Numerators and pole multiplicities must be committed before `alpha` (spec §4.1).
    #[test]
    fn initial_column_rules() {
        let (c, _) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        assert!(c.check().is_ok());
        let n_mm = c.n_p + c.n_m;
        // a pole term on a w_P column
        let mut x = c.clone();
        x.recip[0].terms.push((n_mm, Scalar::ONE, Some(Scalar::ONE.into())));
        assert!(x.check().is_err());
        // a multiplicity in a LinR slot (committed after alpha)
        let mut x = c.clone();
        x.partition[0] = (Slot::LinR, 0);
        assert!(x.check().is_err());
        // a numerator reading w_P
        let mut x = c.clone();
        let mut w_n = SparseMatrix::new(x.w_n.n_cols());
        w_n.push_row(vec![(n_mm + 1, Scalar::ONE)]);
        for _ in 1..x.n_p {
            w_n.push_row(vec![]);
        }
        x.w_n = w_n;
        assert!(x.check().is_err());
        // inputs must not spill from the ordinary linear rows into the reciprocal rows
        let mut x = c.clone();
        x.w_l = SparseMatrix::new(x.w_l.n_cols());
        x.a_l.clear();
        assert!(x.check().is_err());
        // an ordinary linear row may read anything
        let mut x = c.clone();
        x.w_l.push_row(vec![(n_mm, Scalar::ONE), (2 * n_mm + 1, Scalar::ONE)]);
        x.a_l.push(Scalar::ZERO);
        assert!(x.check().is_ok());
    }

    /// Nothing committed after `alpha` (`w_R`, `LinR` slots) may enter a numerator or a
    /// reciprocal row, with or without a pole; the verifier rejects (without panicking) a
    /// circuit that breaks the rules. Found in review: these rules carry soundness.
    #[test]
    fn late_columns_are_rejected() {
        let (c, _) = range_proof(4, 3, &digits_of(37, 4, 3), false); // inline: n_m = 1
        assert!(c.check().is_ok());
        let n_mm = c.n_p + c.n_m;
        let w_r_col = n_mm + c.n_p;
        let numerator_on = |col: usize, c: &ReciprocalCircuit| {
            let mut x = c.clone();
            let mut w_n = SparseMatrix::new(x.w_n.n_cols());
            w_n.push_row(vec![(col, Scalar::ONE)]);
            for _ in 1..x.n_p {
                w_n.push_row(vec![]);
            }
            x.w_n = w_n;
            x
        };
        let mut x = c.clone();
        x.recip[0].terms.push((w_r_col, Scalar::ONE, None));
        assert!(x.check().is_err(), "pole-free term on w_R");
        assert!(numerator_on(w_r_col, &c).check().is_err(), "numerator on w_R");
        assert!(numerator_on(0, &c).check().is_ok(), "numerator on w_D");

        // a LinR element: allowed in ordinary rows, not in numerators or reciprocal rows
        let (mut s, _) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        let lin_r_col = 2 * (s.n_p + s.n_m) + 3;
        s.recip[0].terms.retain(|t| t.0 != lin_r_col); // drop the pole on m_3
        s.partition[3] = (Slot::LinR, 3);
        assert!(s.check().is_ok());
        let mut x = s.clone();
        x.recip[0].terms.push((lin_r_col, Scalar::ONE, None));
        assert!(x.check().is_err(), "pole-free term on a LinR element");
        assert!(numerator_on(lin_r_col, &s).check().is_err(), "numerator on a LinR element");
        let mut x = s.clone();
        x.w_l.push_row(vec![(lin_r_col, Scalar::ONE)]);
        x.a_l.push(Scalar::ZERO);
        assert!(x.check().is_ok(), "ordinary row on a LinR element");

        // the verifier checks the circuit (rules and column ranges) and fails cleanly
        let (c, w) = range_proof(4, 3, &digits_of(37, 4, 3), false);
        let (pc, bp) = setup(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let V = inputs(&g, &w);
        let proof = prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
        let mut bad = c.clone();
        bad.recip[0].terms.push((w_r_col, Scalar::ONE, None));
        assert!(verify(&proof, &bad, &g, &V, &mut Transcript::new(b"t")).is_err());
        let mut oob = c.clone();
        oob.recip[0].terms.push((10_000, Scalar::ONE, None));
        assert!(oob.check().is_err());
        assert!(verify(&proof, &oob, &g, &V, &mut Transcript::new(b"t")).is_err());
        // generators of another shape
        let bp2 = BulletproofGens::new(64, 1);
        let g2 = BpppGens::new(&pc, &bp2, c.n_lin + 1, c.n_p + c.n_m).unwrap();
        assert!(verify(&proof, &c, &g2, &V, &mut Transcript::new(b"t")).is_err());
    }

    /// A reciprocal row must vanish as a rational function, not just at one alpha: an
    /// out-of-range digit with multiplicities tuned to a known alpha passes the compiled check
    /// at that alpha but is not a satisfying witness. Found in review.
    #[test]
    fn satisfaction_is_identity_in_x() {
        let (c, mut w) = range_proof(4, 3, &[1, 4, 2], true);
        let alpha = Scalar::from(10u64);
        let m3 = (alpha + Scalar::from(3u64)) * (alpha + Scalar::from(4u64)).invert();
        w.w_o = vec![Scalar::ZERO, Scalar::ONE, Scalar::ONE, m3];
        let compiled = c.compile(Scalar::ZERO, alpha).unwrap();
        let w_p = c.reciprocals(&w, alpha).unwrap();
        assert!(compiled.is_satisfied(&c.compiled_witness(&w, w_p)));
        assert!(!c.is_satisfied(&w, Scalar::ZERO, alpha));
        // multiplicities summing to the number of digits (so lumping all poles together would
        // cancel), tuned so that f(alpha) = 0: m_0 = x, m_3 = 1 - x, x = -alpha / (3 (alpha + 4))
        let x = -alpha * (Scalar::from(3u64) * (alpha + Scalar::from(4u64))).invert();
        w.w_o = vec![x, Scalar::ONE, Scalar::ONE, Scalar::ONE - x];
        let w_p = c.reciprocals(&w, alpha).unwrap();
        assert!(compiled.is_satisfied(&c.compiled_witness(&w, w_p)));
        assert!(!c.is_satisfied(&w, Scalar::ZERO, alpha));
    }

    /// A public pole at `-alpha` is undefined: the prover fails and the verifier rejects.
    #[test]
    fn public_pole_at_alpha_fails() {
        let mut rng = ChaCha20Rng::seed_from_u64(34);
        let (c, w) = range_proof(4, 3, &digits_of(37, 4, 3), true); // digits 1, 1, 2; poles 0..3
        let (pc, bp) = setup(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let V = inputs(&g, &w);
        let mut chal: Vec<Scalar> = (5..40u64).map(Scalar::from).collect();
        let proof = prove(&c, &g, &V, &w, &mut Replay::new(chal.clone()), &mut rng).unwrap();
        chal[0] = -Scalar::from(3u64);
        assert!(prove(&c, &g, &V, &w, &mut Replay::new(chal.clone()), &mut rng).is_err());
        assert!(verify(&proof, &c, &g, &V, &mut Replay::new(chal)).is_err());
    }

    /// Rebuild a matrix with more columns (inserting none: the new columns are at the end of
    /// `w_O`, after every existing column).
    fn widen(m: &SparseMatrix, n_cols: usize) -> SparseMatrix {
        let mut out = SparseMatrix::new(n_cols);
        for r in 0..m.n_rows() {
            out.push_row(m.row(r).map(|(c, v)| (c, *v)));
        }
        out
    }

    /// Ordinary rows that read reciprocals: `w_R,0 = 2 w_P,0` and a `LinR` element
    /// `y = w_P,1 + 1`. These values depend on alpha; the two-phase prover computes them in the
    /// callback (spec §4.3) and produces exactly the proof of the one-phase prover given the
    /// same values.
    #[test]
    fn two_phase_prover_takes_late_values_from_callback() {
        let (mut c, mut w) = range_proof(4, 3, &digits_of(37, 4, 3), false); // n_p = 3, n_m = 1
        let n_mm = c.n_p + c.n_m;
        let n_w = 2 * n_mm + c.n_o + 1;
        let y_col = 2 * n_mm + c.n_o;
        c.w_n = widen(&c.w_n, n_w);
        c.w_m = widen(&c.w_m, n_w);
        c.w_l = widen(&c.w_l, n_w);
        c.w_l.push_row(vec![(n_mm + c.n_p, Scalar::ONE), (n_mm, -Scalar::from(2u64))]);
        c.w_l.push_row(vec![(y_col, Scalar::ONE), (n_mm + 1, -Scalar::ONE)]);
        c.a_l.extend([Scalar::ZERO, -Scalar::ONE]);
        c.n_o += 1;
        c.n_lin = 1;
        c.partition.push((Slot::LinR, 0));
        w.w_o.push(Scalar::from(999u64)); // ignored: replaced by the callback
        w.w_r = vec![Scalar::from(998u64)]; // ignored
        c.check().unwrap();
        let (pc, bp) = setup(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, n_mm).unwrap();
        let V = inputs(&g, &w);
        let chal: Vec<Scalar> = (5..40u64).map(Scalar::from).collect();
        let mut seen = None;
        let late = |alpha: Scalar, w_p: &[Scalar]| {
            seen = Some((alpha, w_p.to_vec()));
            Ok(LateWitness { w_r: vec![Scalar::from(2u64) * w_p[0]], w_o_late: vec![w_p[1] + Scalar::ONE] })
        };
        let mut t = Replay::new(chal.clone());
        let proof = prove_two_phase(&c, &g, &V, &w, late, &mut t, &mut ChaCha20Rng::seed_from_u64(7)).unwrap();
        let (alpha, w_p) = seen.unwrap();
        assert_eq!(alpha, chal[0]);
        assert_eq!(w_p, c.reciprocals_for_test(&w, Scalar::ZERO, alpha));
        verify(&proof, &c, &g, &V, &mut Replay::new(chal.clone())).unwrap();
        // the one-phase prover with the same values gives the same proof
        let mut full = w.clone();
        full.w_r = vec![Scalar::from(2u64) * w_p[0]];
        *full.w_o.last_mut().unwrap() = w_p[1] + Scalar::ONE;
        assert!(c.is_satisfied(&full, Scalar::ZERO, alpha));
        let one = prove(&c, &g, &V, &full, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(7)).unwrap();
        assert_eq!(one, proof);
        // values that ignore alpha do not satisfy the circuit: the prover refuses
        assert!(prove(&c, &g, &V, &w, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(7)).is_err());
        // a callback error or late values of the wrong length are errors
        let bad = |_: Scalar, _: &[Scalar]| Err(ProofError::FormatError);
        assert!(prove_two_phase(&c, &g, &V, &w, bad, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(7)).is_err());
        let short = |_: Scalar, _: &[Scalar]| Ok(LateWitness { w_r: vec![], w_o_late: vec![Scalar::ONE] });
        assert_eq!(
            prove_two_phase(&c, &g, &V, &w, short, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(7)),
            Err(ProofError::FormatError)
        );
        for n in [0usize, 2] {
            let late = move |_: Scalar, _: &[Scalar]| Ok(LateWitness { w_r: vec![Scalar::ONE], w_o_late: vec![Scalar::ONE; n] });
            assert_eq!(
                prove_two_phase(&c, &g, &V, &w, late, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(7)),
                Err(ProofError::FormatError),
                "{} LinR values",
                n
            );
        }
    }

    /// A lookup of 2-tuples (spec §4.1 tuple poles): `n_q` private tuples `(x_q0, x_q1)` in
    /// `w_O`, a public table `rows` with multiplicities in `w_O`; poles `w_D,q = x_q0 + eta x_q1`,
    /// public poles `(r_0, r_1)` as polynomials in `eta`. One reciprocal row:
    /// `sum_q 1/(X + w_D,q) - sum_r m_r/(X + r_0 + eta r_1) = 0`.
    fn tuple_lookup(tuples: &[(Scalar, Scalar)], rows: &[(u64, u64)], mult: &[u64]) -> (ReciprocalCircuit, ReciprocalWitness) {
        let n_p = tuples.len();
        let n_m = 0;
        let n_mm = n_p + n_m;
        let n_o = 2 * n_p + rows.len();
        let n_lin = n_o.saturating_sub(n_mm);
        let n_w = 2 * n_mm + n_o;
        let col_o = |e: usize| 2 * n_mm + e;
        let mut w_n = SparseMatrix::new(n_w);
        (0..n_p).for_each(|_| w_n.push_row(vec![]));
        let mut terms: Vec<(usize, Scalar, Option<Pole>)> = (0..n_p).map(|q| (n_mm + q, Scalar::ONE, None)).collect();
        for (r, &(a, b)) in rows.iter().enumerate() {
            terms.push((col_o(2 * n_p + r), -Scalar::ONE, Some(Pole(vec![Scalar::from(a), Scalar::from(b)]))));
        }
        let comp = |e: usize| Component { terms: vec![(col_o(e), Scalar::ONE)], constant: Scalar::ZERO };
        let c = ReciprocalCircuit {
            n_p,
            n_m,
            n_o,
            n_v: 1,
            n_lin,
            k: 0,
            w_n,
            a_n: vec![Scalar::ONE; n_p],
            w_m: SparseMatrix::new(n_w),
            a_m: vec![],
            w_l: SparseMatrix::new(n_w),
            a_l: vec![],
            recip: vec![ReciprocalRow { terms, consts: vec![] }],
            tuples: (0..n_p).map(|q| TuplePole { pole: q, components: vec![comp(2 * q), comp(2 * q + 1)] }).collect(),
            f_l: false,
            f_m: false,
            partition: (0..n_o).map(|e| if e < n_mm { (Slot::NormO, e) } else { (Slot::LinO, e - n_mm) }).collect(),
        };
        let w_o = tuples.iter().flat_map(|(a, b)| [*a, *b]).chain(mult.iter().map(|m| Scalar::from(*m))).collect();
        // the witness's tuple poles are placeholders (ignored)
        let w = ReciprocalWitness { w_d: (0..n_p).map(|q| Scalar::from(1000 + q as u64)).collect(), w_l: vec![], w_r: vec![], w_o, v: vec![], s: vec![] };
        (c, w)
    }

    fn rows16() -> Vec<(u64, u64)> {
        (0..16u64).map(|i| (i, (i * 7) % 16)).collect()
    }

    fn tuple_gens(c: &ReciprocalCircuit) -> (PedersenGens, BulletproofGens) {
        setup(c)
    }

    /// Tuple poles prove and verify with protocol v2; the transcript is `C_O`, `eta`, `C_L`,
    /// `alpha`, `C_R`; the witness's values of the tuple poles are ignored.
    #[test]
    fn tuple_poles_prove_with_protocol_v2() {
        let rows = rows16();
        let s = |x: u64| Scalar::from(x);
        let (c, w) = tuple_lookup(&[(s(3), s(5)), (s(9), s(15)), (s(3), s(5))], &rows, &{
            let mut m = vec![0u64; 16];
            m[3] = 2;
            m[9] = 1;
            m
        });
        c.check().unwrap();
        assert!(c.uses_eta());
        let (pc, bp) = tuple_gens(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let chal: Vec<Scalar> = (5..40u64).map(Scalar::from).collect();
        let eta = chal[0];
        assert!(c.is_satisfied(&w, eta, chal[1]));
        let mut t = Replay::new(chal.clone());
        let proof = prove(&c, &g, &[], &w, &mut t, &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
        let labels: Vec<&[u8]> = t.log.iter().map(|(l, _)| *l).collect();
        let pos = |l: &[u8]| labels.iter().position(|x| *x == l).unwrap();
        assert_eq!(labels[0], &b"bppp-reciprocal v2"[..]);
        assert!(pos(b"N_t") < pos(b"G") && pos(b"circuit") < pos(b"C_O"));
        assert!(pos(b"C_O") < pos(b"eta") && pos(b"eta") < pos(b"C_L") && pos(b"C_L") < pos(b"alpha"));
        assert!(pos(b"alpha") < pos(b"C_R") && pos(b"C_R") < pos(b"rho"));
        assert_eq!(t.log[pos(b"C_O")].1, proof.C_O.as_bytes().to_vec());
        assert_eq!(t.log[pos(b"C_L")].1, proof.C_L.as_bytes().to_vec());
        let mut tv = Replay::new(chal.clone());
        verify(&proof, &c, &g, &[], &mut tv).unwrap();
        assert_eq!(tv.log, t.log);
        // w_D at eta
        assert_eq!(c.poles_for_test(&w, eta)[1], s(9) + eta * s(15));
        // other placeholders: the same proof
        let mut w2 = w.clone();
        w2.w_d = vec![Scalar::ZERO; 3];
        assert_eq!(prove(&c, &g, &[], &w2, &mut Replay::new(chal.clone()), &mut ChaCha20Rng::seed_from_u64(1)).unwrap(), proof);
        // real transcripts
        let p = prove(&c, &g, &[], &w, &mut Transcript::new(b"tp"), &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
        verify(&p, &c, &g, &[], &mut Transcript::new(b"tp")).unwrap();
        assert!(verify(&p, &c, &g, &[], &mut Transcript::new(b"other")).is_err());
        assert_eq!(proof_from_bytes(&p.to_bytes(), &c).unwrap(), p);
    }

    /// Components are arbitrary field elements: a tuple that packs (base 16) to a table row but
    /// is not one — `(x_0 + 16, x_1 - 1)` — and a tuple with a huge component are not satisfied,
    /// the prover refuses and an unchecked proof does not verify. With packing and no bounds
    /// (phase 6 without the bound rule) the first would pass.
    #[test]
    fn tuples_are_compared_component_by_component() {
        let rows = rows16();
        let s = |x: u64| Scalar::from(x);
        let mut m = vec![0u64; 16];
        m[3] = 1; // row (3, 5)
        let cheats = [(s(3 + 16), s(5) - Scalar::ONE), (s(3) + Scalar::from(1u64 << 63) * s(4), s(5)), (s(5), s(3))];
        for (i, &cheat) in cheats.iter().enumerate() {
            let (c, w) = tuple_lookup(&[cheat], &rows, &m);
            let (pc, bp) = tuple_gens(&c);
            let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
            assert!(!c.is_satisfied(&w, Scalar::from(77u64), Scalar::from(5u64)), "cheat {}", i);
            let mut rng = ChaCha20Rng::seed_from_u64(3);
            assert!(prove(&c, &g, &[], &w, &mut Transcript::new(b"tp"), &mut rng).is_err(), "cheat {}", i);
            let proof = prove_impl(&c, &g, &[], &w, &mut Transcript::new(b"tp"), &mut rng, false).unwrap();
            assert!(verify(&proof, &c, &g, &[], &mut Transcript::new(b"tp")).is_err(), "cheat {}", i);
        }
        // at eta = 16 the compression is the packing: the first cheat collides there (a bad
        // challenge, spec §4.7), as it would for every eta with packing
        let (c, w) = tuple_lookup(&[cheats[0]], &rows, &m);
        assert!(c.is_satisfied(&w, Scalar::from(16u64), Scalar::from(5u64)));
        let (ac, aw) = c.compiled_for_test(&w, Scalar::from(16u64), Scalar::from(5u64));
        assert!(ac.is_satisfied(&aw));
    }

    /// The rules of spec §4.1 for tuple poles: components on early columns only (not `C_L`:
    /// `w_D`, `w_L`, `LinL`; not `C_R`: `w_P`, `w_R`, `LinR`), poles increasing and in range, at
    /// least one component, pole polynomials not empty.
    #[test]
    fn tuple_pole_rules() {
        let s = |x: u64| Scalar::from(x);
        let (c, _) = tuple_lookup(&[(s(3), s(5)), (s(9), s(15))], &rows16(), &[0; 16]);
        c.check().unwrap();
        let n_mm = c.n_p + c.n_m;
        let on = |col: usize| {
            let mut x = c.clone();
            x.tuples[0].components[1].terms.push((col, Scalar::ONE));
            x
        };
        assert!(on(0).check().is_err(), "w_D");
        assert!(on(n_mm).check().is_err(), "w_P");
        assert!(on(2 * n_mm + 1).check().is_ok(), "NormO");
        assert!(on(2 * n_mm + 10).check().is_ok(), "LinO");
        assert!(on(2 * n_mm + c.n_o).check().is_err(), "out of range");
        for slot in [Slot::LinL, Slot::LinR] {
            let mut x = on(2 * n_mm + 10);
            x.partition[10] = (slot, 9);
            assert!(x.check().is_err(), "{:?}", slot as u8);
        }
        let mut x = c.clone();
        x.tuples.swap(0, 1);
        assert!(x.check().is_err(), "order");
        let mut x = c.clone();
        x.tuples[1].pole = 0;
        assert!(x.check().is_err(), "twice");
        let mut x = c.clone();
        x.tuples[1].pole = 2;
        assert!(x.check().is_err(), "range");
        let mut x = c.clone();
        x.tuples[0].components.clear();
        assert!(x.check().is_err(), "no component");
        let mut x = c.clone();
        x.recip[0].terms[2].2 = Some(Pole(vec![]));
        assert!(x.check().is_err(), "empty pole");
        let mut x = c.clone();
        x.recip[0].consts.push((Scalar::ONE, Some(Pole(vec![]))));
        assert!(x.check().is_err(), "empty constant pole");
        // a free pole must not sit next to tuple poles (free_and_tuple_poles_do_not_mix)
        let mut x = c.clone();
        x.tuples.remove(0);
        assert!(x.check().is_err());
        // without tuple poles and long poles the circuit is v1
        let mut x = c.clone();
        x.tuples.clear();
        x.recip[0].terms.iter_mut().for_each(|t| t.2 = t.2.take().map(|p| Pole(p.0[..1].to_vec())));
        assert!(!x.uses_eta());
    }

    /// v2 proofs in a batch (spec §3.11) next to v1 proofs; a bad one fails the batch.
    #[test]
    fn tuple_poles_batch() {
        let s = |x: u64| Scalar::from(x);
        let mut m = vec![0u64; 16];
        m[3] = 1;
        let (c, w) = tuple_lookup(&[(s(3), s(5))], &rows16(), &m);
        let (r, rw) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(64, 1);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_p + c.n_m).unwrap();
        let gr = BpppGens::new(&pc, &bp, r.n_lin, r.n_p + r.n_m).unwrap();
        let Vr = inputs(&gr, &rw);
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let p1 = prove(&c, &g, &[], &w, &mut Transcript::new(b"b"), &mut rng).unwrap();
        let p2 = prove(&r, &gr, &Vr, &rw, &mut Transcript::new(b"b"), &mut rng).unwrap();
        let run = |p1: &CircuitProof| {
            let mut b = crate::bppp::BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(1));
            b.add_reciprocal(p1, &c, &[], &mut Transcript::new(b"b"))?;
            b.add_reciprocal(&p2, &r, &Vr, &mut Transcript::new(b"b"))?;
            b.verify()
        };
        run(&p1).unwrap();
        let mut bad = p1.clone();
        bad.C_O = p2.C_O;
        assert!(run(&bad).is_err());
    }

    /// An eta-row (a tuple pole's reciprocal, or a pole polynomial of length 2 or more) must not
    /// read a free pole's reciprocal (spec §4.1, found in review: a free pole is committed after
    /// eta and could cancel any tuple). Rows without them are unrestricted.
    #[test]
    fn free_and_tuple_poles_do_not_mix() {
        let s = |x: u64| Scalar::from(x);
        let (c, _) = tuple_lookup(&[(s(3), s(5)), (s(9), s(15))], &rows16(), &[0; 16]);
        let n_mm = c.n_p + c.n_m;
        // pole 0 free: its reciprocal sits in a row with the tuple pole 1
        let mut x = c.clone();
        x.tuples.remove(0);
        assert!(x.check().is_err(), "free and tuple pole in one row");
        // pole 0 free in a row of its own (v1-style, constant pole): fine
        let mut y = x.clone();
        y.recip[0].terms.remove(0);
        y.recip.push(ReciprocalRow { terms: vec![(n_mm, Scalar::ONE, None)], consts: vec![(-Scalar::ONE, Some(s(7).into()))] });
        assert!(y.check().is_ok());
        // ... but not next to a pole polynomial of length 2, as a term or as a constant
        let mut z = y.clone();
        z.recip[1].consts.push((Scalar::ONE, Some(Pole(vec![s(1), s(2)]))));
        assert!(z.check().is_err(), "free pole and a long constant pole");
        let mut z = y.clone();
        z.recip[1].terms.push((2 * n_mm, Scalar::ONE, Some(Pole(vec![s(1), s(2)]))));
        assert!(z.check().is_err(), "free pole and a long term pole");
        // a long pole of length 2 with zeros is still long; a row without any reciprocal is free
        let mut z = y.clone();
        z.recip.push(ReciprocalRow { terms: vec![], consts: vec![(Scalar::ONE, Some(Pole(vec![s(1), s(2)]))), (-Scalar::ONE, Some(Pole(vec![s(1), s(2)])))] });
        assert!(z.check().is_ok(), "public-only eta-row");
    }

    /// The v2 digest covers the tuple poles and the pole polynomials; v1 circuits keep the v1
    /// digest (regression pins and vectors), and a length-1 pole hashes differently in v2.
    #[test]
    fn digest_v2_covers_tuple_poles() {
        let s = |x: u64| Scalar::from(x);
        let (c, _) = tuple_lookup(&[(s(3), s(5)), (s(9), s(15))], &rows16(), &[0; 16]);
        let d = c.digest();
        let mut x = c.clone();
        x.tuples[1].components[0].constant = Scalar::ONE;
        assert_ne!(x.digest(), d, "constant");
        let mut x = c.clone();
        x.tuples[1].components[0].terms[0].1 = s(2);
        assert_ne!(x.digest(), d, "coefficient");
        let mut x = c.clone();
        x.tuples[1].components.swap(0, 1);
        assert_ne!(x.digest(), d, "component order");
        let mut x = c.clone();
        x.tuples[1].components.push(Component { terms: vec![], constant: Scalar::ZERO });
        assert_ne!(x.digest(), d, "a zero component");
        let mut x = c.clone();
        x.recip[0].terms[2].2.as_mut().unwrap().0.push(Scalar::ZERO);
        assert_ne!(x.digest(), d, "a zero coefficient of a pole");
        let mut x = c.clone();
        x.tuples.remove(0);
        assert_ne!(x.digest(), d, "number of tuple poles");
    }

    #[test]
    fn digest_covers_reciprocal_rows() {
        let (c, _) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        let d = c.digest();
        let mut x = c.clone();
        x.recip[0].terms[3].2 = Some(Scalar::from(9u64).into());
        assert_ne!(x.digest(), d);
        let mut x = c.clone();
        x.recip[0].consts.push((Scalar::ONE, None));
        assert_ne!(x.digest(), d);
        let mut x = c.clone();
        x.a_n[0] = Scalar::from(2u64);
        assert_ne!(x.digest(), d);
        let mut x = c.clone();
        x.partition.swap(0, 1);
        assert_ne!(x.digest(), d, "partition");
        let mut x = c.clone();
        let mut w_l = SparseMatrix::new(c.w_l.n_cols());
        w_l.push_row(c.w_l.row(0).map(|(col, v)| (col, v + Scalar::ONE)));
        x.w_l = w_l;
        assert_ne!(x.digest(), d, "W_l coefficients");
        let mut x = c.clone();
        x.w_m.push_row(vec![]);
        x.a_m.push(Scalar::ZERO);
        x.n_m += 1;
        assert_ne!(x.digest(), d, "W_m");
        let mut x = c.clone();
        x.f_m = true;
        assert_ne!(x.digest(), d, "flags");
        let mut x = c.clone();
        x.n_lin += 1;
        assert_ne!(x.digest(), d, "dimensions");
        let mut x = c.clone();
        x.recip[0].terms[0].1 = Scalar::from(2u64);
        assert_ne!(x.digest(), d, "coefficient");
    }
}

//! Reciprocal form circuits (spec §4, paper §6.2–6.3).
//!
//! An arithmetic circuit with `n_p` poles: private denominators `w_D` committed with the
//! initial witness, reciprocals `w_P,i = num_i / (alpha + w_D,i)` committed after the challenge
//! `alpha`, and reciprocal rows that must vanish as rational functions. For a fixed `alpha` the
//! circuit compiles to an [`ArithmeticCircuit`] proven with the inner protocol of spec §3.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};
use sha3::{Digest, Sha3_256};

use super::circuit::{self, ArithmeticCircuit, CircuitProof, CircuitWitness, Slot};
use super::gens::BpppGens;
use super::sparse::SparseMatrix;
use super::transcript::BpppTranscript;
use crate::errors::ProofError;

/// A reciprocal row (spec §4.1): `sum c * w'[col] / (X + t)` over the terms (no pole: `c *
/// w'[col]`) plus `sum c / (X + t)` over the constants (no pole: `c`), which must vanish.
#[derive(Clone, Debug, PartialEq)]
pub struct ReciprocalRow {
    /// `(column of w', coefficient, pole)`.
    pub terms: Vec<(usize, Scalar, Option<Scalar>)>,
    /// `(coefficient, pole)`.
    pub consts: Vec<(Scalar, Option<Scalar>)>,
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
        for row in &self.recip {
            for &(c, _, pole) in &row.terms {
                let ok = c < n_w
                    && match (self.col(c), pole) {
                        (Col::Initial, _) => true,
                        (Col::Reciprocal(_), None) => true,
                        _ => false,
                    };
                if !ok {
                    return bad;
                }
            }
        }
        self.compile_with(|_| Some(Scalar::ONE), Scalar::ONE)?.check()
    }

    /// The compiled circuit, with `coef(pole)` the factor of a term with that pole (`None`
    /// when undefined) and `alpha` the coefficient subtracted at the reciprocal columns.
    fn compile_with<F: Fn(Scalar) -> Option<Scalar>>(&self, coef: F, alpha: Scalar) -> Result<ArithmeticCircuit, ProofError> {
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
        let factor = |pole: Option<Scalar>| match pole {
            None => Ok(Scalar::ONE),
            Some(t) => coef(t).ok_or(ProofError::VerificationError),
        };
        for row in &self.recip {
            let mut terms = Vec::with_capacity(row.terms.len());
            for &(c, v, pole) in &row.terms {
                terms.push((c, v * factor(pole)?));
            }
            w_l.push_row(terms);
            let mut a = Scalar::ZERO;
            for &(v, pole) in &row.consts {
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

    /// The compiled circuit for the challenge `alpha` (spec §4.2); an error if a public pole
    /// `t` has `alpha + t = 0`.
    fn compile(&self, alpha: Scalar) -> Result<ArithmeticCircuit, ProofError> {
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
        )
    }

    /// The reciprocal circuit digest (spec §4.4).
    pub fn digest(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(b"bppp-reciprocal-digest v1");
        for x in self.dims() {
            h.update(x.to_le_bytes());
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
        let pole = |h: &mut Sha3_256, p: &Option<Scalar>| match p {
            None => h.update([0u8]),
            Some(t) => {
                h.update([1u8]);
                h.update(t.as_bytes());
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

    /// Whether `w` satisfies the circuit: every reciprocal row vanishes as a rational function
    /// of `X` (all multiplicities per pole value and the polynomial part are zero), and the
    /// compiled circuit holds at `alpha` (for rows that read reciprocals).
    pub fn is_satisfied(&self, w: &ReciprocalWitness, alpha: Scalar) -> bool {
        if self.check().is_err() || self.check_witness(w).is_err() {
            return false;
        }
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
            for &(c, v, pole) in &row.terms {
                match self.col(c) {
                    Col::Reciprocal(i) => add(Some(w.w_d[i]), v * num[i]),
                    _ => add(pole, v * full[c]),
                }
            }
            for &(v, pole) in &row.consts {
                add(pole, v);
            }
            if poly != Scalar::ZERO || poles.iter().any(|(_, m)| *m != Scalar::ZERO) {
                return false;
            }
        }
        match (self.reciprocals(w, alpha), self.compile(alpha)) {
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
    t.domain_sep(b"bppp-reciprocal v1");
    let labels: [&'static [u8]; 10] =
        [b"N_p", b"N_m", b"N_O", b"N_v", b"N_lin", b"k", b"N_l", b"N_r", b"f_l", b"f_m"];
    for (label, x) in labels.iter().zip(c.dims()) {
        t.append_u64(label, x);
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
    prove_impl(c, gens, V, w, transcript, rng, true)
}

fn prove_impl<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ReciprocalCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &ReciprocalWitness,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError> {
    check_gens(c, gens)?;
    c.check()?;
    c.check_witness(w)?;
    if V.len() != c.k {
        return Err(ProofError::FormatError);
    }
    let w_l: Vec<Scalar> = w.w_d.iter().chain(&w.w_l).copied().collect();
    let ol = circuit::commit_ol(gens, c.n_lin, &c.partition, &w_l, &w.w_o, rng);
    absorb_statement(transcript, c, gens, V);
    transcript.append_point(b"C_L", &ol.C_L);
    transcript.append_point(b"C_O", &ol.C_O);
    let alpha = transcript.challenge(b"alpha");
    let w_p = c.reciprocals(w, alpha)?;
    let compiled = c.compile(alpha)?;
    let cw = c.compiled_witness(w, w_p);
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
    check_gens(c, gens)?;
    c.check().map_err(|_| ProofError::VerificationError)?;
    if V.len() != c.k {
        return Err(ProofError::VerificationError);
    }
    absorb_statement(transcript, c, gens, V);
    transcript.append_point(b"C_L", &proof.C_L);
    transcript.append_point(b"C_O", &proof.C_O);
    let alpha = transcript.challenge(b"alpha");
    let compiled = c.compile(alpha)?;
    transcript.append_point(b"C_R", &proof.C_R);
    proof.verify_inner(&compiled, gens, V, transcript)
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
            .chain((0..b).map(|s| (2 * n_mm + s, -Scalar::ONE, Some(Scalar::from(s as u64)))))
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

    /// Hands out the given scalars to `Scalar::random` (see the circuit tests).
    struct ScalarRng(alloc::collections::VecDeque<u8>);

    impl ScalarRng {
        fn new(scalars: &[Scalar]) -> Self {
            let mut q = alloc::collections::VecDeque::new();
            for s in scalars {
                q.extend(s.to_bytes().iter());
                q.extend([0u8; 32].iter());
            }
            ScalarRng(q)
        }
    }

    impl rand_core::RngCore for ScalarRng {
        fn next_u32(&mut self) -> u32 {
            unimplemented!()
        }
        fn next_u64(&mut self) -> u64 {
            unimplemented!()
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            dest.iter_mut().for_each(|b| *b = self.0.pop_front().expect("more randomness than in the vector"));
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }

    impl rand_core::CryptoRng for ScalarRng {}

    fn sc(v: &serde_json::Value) -> Scalar {
        use core::convert::TryInto;
        let b: [u8; 32] = hex::decode(v.as_str().unwrap()).unwrap().try_into().unwrap();
        Scalar::from_canonical_bytes(b).unwrap()
    }

    fn scs(v: &serde_json::Value) -> Vec<Scalar> {
        v.as_array().unwrap().iter().map(sc).collect()
    }

    fn sparse_from(v: &serde_json::Value, cols: usize) -> SparseMatrix {
        let mut m = SparseMatrix::new(cols);
        for row in v.as_array().unwrap() {
            m.push_row(row.as_array().unwrap().iter().map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]))));
        }
        m
    }

    fn pole(v: &serde_json::Value) -> Option<Scalar> {
        if v.is_null() {
            None
        } else {
            Some(sc(v))
        }
    }

    /// The prover reproduces the independent Python reference
    /// (`tests/vectors/bppp/reciprocal.json`): reciprocals, commitments, norm argument; the
    /// verifier accepts exactly the satisfied cases.
    #[test]
    fn matches_reference_vectors() {
        let file: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/bppp/reciprocal.json")).unwrap();
        let pc = PedersenGens::default();
        for case in file["cases"].as_array().unwrap() {
            let name = case["name"].as_str().unwrap();
            let u = |k: &str| case[k].as_u64().unwrap() as usize;
            let (n_p, n_m, n_o, n_lin) = (u("n_p"), u("n_m"), u("n_o"), u("n_lin"));
            let n_w = 2 * (n_p + n_m) + n_o;
            let slot = |s: &str| match s {
                "nO" => Slot::NormO,
                "lO" => Slot::LinO,
                "lL" => Slot::LinL,
                "lR" => Slot::LinR,
                _ => panic!("slot {}", s),
            };
            let c = ReciprocalCircuit {
                n_p,
                n_m,
                n_o,
                n_v: u("n_v"),
                n_lin,
                k: u("k"),
                w_n: sparse_from(&case["w_n"], n_w),
                a_n: scs(&case["a_n"]),
                w_m: sparse_from(&case["w_m"], n_w),
                a_m: scs(&case["a_m"]),
                w_l: sparse_from(&case["w_l"], n_w),
                a_l: scs(&case["a_l"]),
                recip: case["recip"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|r| ReciprocalRow {
                        terms: r["terms"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .map(|t| (t[0].as_u64().unwrap() as usize, sc(&t[1]), pole(&t[2])))
                            .collect(),
                        consts: r["consts"].as_array().unwrap().iter().map(|t| (sc(&t[0]), pole(&t[1]))).collect(),
                    })
                    .collect(),
                f_l: u("f_l") == 1,
                f_m: u("f_m") == 1,
                partition: case["partition"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|p| (slot(p[0].as_str().unwrap()), p[1].as_u64().unwrap() as usize))
                    .collect(),
            };
            assert_eq!(c.w_l.n_rows(), u("n_l"), "{}", name);
            c.check().unwrap_or_else(|e| panic!("{}: {:?}", name, e));
            let w = ReciprocalWitness {
                w_d: scs(&case["w_D"]),
                w_l: scs(&case["w_L"]),
                w_r: scs(&case["w_R"]),
                w_o: scs(&case["w_O"]),
                v: case["v"].as_array().unwrap().iter().map(scs).collect(),
                s: scs(&case["s"]),
            };
            let ch = &case["chal"];
            let alpha = sc(&ch["alpha"]);
            let satisfied = case["satisfied"].as_bool().unwrap();
            assert_eq!(c.is_satisfied(&w, alpha), satisfied, "{}: satisfied", name);
            assert_eq!(c.reciprocals(&w, alpha).unwrap(), scs(&case["w_P"]), "{}: w_P", name);
            let bp = BulletproofGens::new((n_p + n_m).max(n_lin + 6), 1);
            let g = BpppGens::new(&pc, &bp, n_lin, n_p + n_m).unwrap();
            let point = |p: &serde_json::Value| {
                use curve25519_dalek::traits::MultiscalarMul;
                (g.g * sc(&p["g"])
                    + curve25519_dalek::ristretto::RistrettoPoint::multiscalar_mul(scs(&p["h"]), &g.h)
                    + curve25519_dalek::ristretto::RistrettoPoint::multiscalar_mul(scs(&p["n"]), g.n))
                .compress()
            };
            let V = inputs(&g, &w);
            for (i, p) in case["V"].as_array().unwrap().iter().enumerate() {
                assert_eq!(V[i], point(p), "{}: V_{}", name, i);
            }
            let r = &case["rand"];
            let randomness: Vec<Scalar> = ["r_O", "r_L", "r_R", "l_S", "n_S"].iter().flat_map(|k| scs(&r[*k])).collect();
            let challenges: Vec<Scalar> = ["alpha", "rho", "lambda", "beta", "delta", "tau"]
                .iter()
                .map(|k| sc(&ch[*k]))
                .chain(scs(&case["gammas"]))
                .collect();
            let proof =
                prove_impl(&c, &g, &V, &w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness), false)
                    .unwrap();
            let checked = prove(&c, &g, &V, &w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness));
            assert_eq!(checked.is_ok(), satisfied, "{}: prover check", name);
            assert_eq!(proof.C_L, point(&case["C_L"]), "{}: C_L", name);
            assert_eq!(proof.C_R, point(&case["C_R"]), "{}: C_R", name);
            assert_eq!(proof.C_O, point(&case["C_O"]), "{}: C_O", name);
            assert_eq!(proof.C_S, point(&case["C_S"]), "{}: C_S", name);
            let rounds = case["rounds"].as_array().unwrap();
            assert_eq!(proof.wnla.X.len(), rounds.len(), "{}: rounds", name);
            for (i, round) in rounds.iter().enumerate() {
                assert_eq!(proof.wnla.X[i], point(&round["X"]), "{}: X_{}", name, i);
                assert_eq!(proof.wnla.R[i], point(&round["R"]), "{}: R_{}", name, i);
            }
            assert_eq!(proof.wnla.l, scs(&case["l_final"]), "{}: l", name);
            assert_eq!(proof.wnla.n, scs(&case["n_final"]), "{}: n", name);
            let verdict = verify(&proof, &c, &g, &V, &mut Replay::new(challenges)).is_ok();
            assert_eq!(verdict, case["verifies"].as_bool().unwrap(), "{}: verdict", name);
        }
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
            assert!(!c.is_satisfied(&w, Scalar::from(12345u64)));
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
        x.recip[0].terms.push((n_mm, Scalar::ONE, Some(Scalar::ONE)));
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

    #[test]
    fn digest_covers_reciprocal_rows() {
        let (c, _) = range_proof(4, 3, &digits_of(37, 4, 3), true);
        let d = c.digest();
        let mut x = c.clone();
        x.recip[0].terms[3].2 = Some(Scalar::from(9u64));
        assert_ne!(x.digest(), d);
        let mut x = c.clone();
        x.recip[0].consts.push((Scalar::ONE, None));
        assert_ne!(x.digest(), d);
        let mut x = c.clone();
        x.a_n[0] = Scalar::from(2u64);
        assert_ne!(x.digest(), d);
    }
}

//! Arithmetic circuit protocol (spec §3, paper §5).
//!
//! Proves `W_l w + f_l w_V + a_l = 0` and `w_L ∘ w_R = W_m w + f_m w_V + a_m` for a witness
//! `w = w_L || w_R || w_O` and committed input vectors `w_V`: commitments `C_L`, `C_R`, `C_O`,
//! challenges, a blinding commitment `C_S`, and one weighted norm linear argument.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};
use sha3::{Digest, Sha3_256};

use super::gens::{BpppGens, H_FIXED};
use super::poly::{pow_signed, Poly, VecPoly};
use super::sparse::SparseMatrix;
pub(crate) use super::terms::Terms;
use super::transcript::BpppTranscript;
use super::wnla::{self, WnlaProof, WnlaStatement};
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};
use crate::util;

/// Where an element of `w_O` is committed (spec §3.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// Norm part of `C_O`, index `< n_m`.
    NormO = 0,
    /// Linear part of `C_O`, index `< n_lin`.
    LinO = 1,
    /// Linear part of `C_L`, index `< n_lin`.
    LinL = 2,
    /// Linear part of `C_R`, index `< n_lin`.
    LinR = 3,
}

/// An arithmetic circuit (spec §3.1): the witness `w = w_L || w_R || w_O` (columns of `w_l`
/// and `w_m`) and inputs `w_V = v_0 || ... || v_{k-1}` satisfy
/// `w_l w + f_l w_V + a_l = 0` and `w_L ∘ w_R = w_m w + f_m w_V + a_m`.
#[derive(Clone, Debug, PartialEq)]
pub struct ArithmeticCircuit {
    /// Number of multiplications, `|w_L| = |w_R|`; at least 1.
    pub n_m: usize,
    /// `|w_O|`.
    pub n_o: usize,
    /// Length of each input vector; at least 1.
    pub n_v: usize,
    /// Length of the linear part of the commitments; at least `n_v - 1`.
    pub n_lin: usize,
    /// Number of input vectors.
    pub k: usize,
    /// Linear constraints, `n_l x (2 n_m + n_o)`.
    pub w_l: SparseMatrix,
    /// Affine term of the linear constraints.
    pub a_l: Vec<Scalar>,
    /// Multiplicative constraints, `n_m x (2 n_m + n_o)`.
    pub w_m: SparseMatrix,
    /// Affine term of the multiplicative constraints.
    pub a_m: Vec<Scalar>,
    /// Whether the inputs enter the first `k n_v` linear constraints.
    pub f_l: bool,
    /// Whether the inputs enter the first `k n_v` multiplicative constraints.
    pub f_m: bool,
    /// The slot of each element of `w_O`; injective.
    pub partition: Vec<(Slot, usize)>,
}

/// A witness for an [`ArithmeticCircuit`]. Its `Debug` shows only the dimensions.
#[derive(Clone)]
pub struct CircuitWitness {
    /// Left inputs of the multiplications.
    pub w_l: Vec<Scalar>,
    /// Right inputs of the multiplications.
    pub w_r: Vec<Scalar>,
    /// Further witness elements.
    pub w_o: Vec<Scalar>,
    /// The input vectors.
    pub v: Vec<Vec<Scalar>>,
    /// Blindings of the input commitments.
    pub s: Vec<Scalar>,
}

impl core::fmt::Debug for CircuitWitness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "CircuitWitness {{ n_m: {}, n_o: {}, inputs: {} }}",
            self.w_l.len(),
            self.w_o.len(),
            self.v.len()
        )
    }
}

/// A circuit proof: four commitments and a norm argument.
#[derive(Clone, Debug, PartialEq)]
pub struct CircuitProof {
    /// Commitment to `w_L` (and the `LinL` slots).
    pub C_L: CompressedRistretto,
    /// Commitment to `w_R` (and the `LinR` slots).
    pub C_R: CompressedRistretto,
    /// Commitment to the `NormO` and `LinO` slots.
    pub C_O: CompressedRistretto,
    /// Blinding commitment.
    pub C_S: CompressedRistretto,
    /// The norm argument.
    pub wnla: WnlaProof,
}

/// Exponents of `c_r(T) = beta (T^-1, T, T^2, T^3, T^5, T^6, T^7)` (spec §3.5).
const E_R: [i32; 7] = [-1, 1, 2, 3, 5, 6, 7];

fn flag(f: bool) -> Scalar {
    if f {
        Scalar::ONE
    } else {
        Scalar::ZERO
    }
}

fn ip(a: &[Scalar], b: &[Scalar]) -> Scalar {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

fn scaled(v: &[Scalar], x: Scalar) -> Vec<Scalar> {
    v.iter().map(|a| a * x).collect()
}

fn added(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    a.iter().zip(b).map(|(x, y)| x + y).collect()
}

fn draw<R: RngCore + CryptoRng>(rng: &mut R, n: usize) -> Vec<Scalar> {
    (0..n).map(|_| Scalar::random(rng)).collect()
}

impl ArithmeticCircuit {
    /// Number of linear constraints.
    pub fn n_l(&self) -> usize {
        self.w_l.n_rows()
    }

    fn dims(&self) -> [u64; 8] {
        [self.n_m, self.n_o, self.n_v, self.n_lin, self.k, self.n_l(), self.f_l as usize, self.f_m as usize]
            .map(|x| x as u64)
    }

    /// Check the shape: dimensions, matrix sizes, flags and an injective partition.
    pub fn check(&self) -> Result<(), ProofError> {
        let bad = Err(ProofError::FormatError);
        let n_w = self.n_m.checked_mul(2).and_then(|x| x.checked_add(self.n_o));
        let kv = self.k.checked_mul(self.n_v);
        let (n_w, kv) = match (n_w, kv) {
            (Some(n_w), Some(kv)) => (n_w, kv),
            _ => return bad,
        };
        if self.n_m == 0 || self.n_v == 0 || self.n_v > self.n_lin.saturating_add(1) {
            return bad;
        }
        if self.w_l.n_cols() != n_w || self.w_m.n_cols() != n_w || self.w_m.n_rows() != self.n_m {
            return bad;
        }
        if self.a_l.len() != self.n_l() || self.a_m.len() != self.n_m {
            return bad;
        }
        if (self.f_l && self.n_l() < kv) || (self.f_m && self.n_m < kv) {
            return bad;
        }
        // Inputs that enter no constraint would not be checked at all.
        if self.k > 0 && !self.f_l && !self.f_m {
            return bad;
        }
        if self.partition.len() != self.n_o {
            return bad;
        }
        // injective and in range; memory proportional to n_o, not to n_m or n_lin
        let mut used: Vec<(u8, usize)> = Vec::with_capacity(self.n_o);
        for &(slot, t) in &self.partition {
            let bound = if slot == Slot::NormO { self.n_m } else { self.n_lin };
            if t >= bound {
                return bad;
            }
            used.push((slot as u8, t));
        }
        used.sort_unstable();
        if used.windows(2).any(|p| p[0] == p[1]) {
            return bad;
        }
        Ok(())
    }

    fn check_witness(&self, w: &CircuitWitness) -> Result<(), ProofError> {
        if w.w_l.len() != self.n_m
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

    fn check_gens(&self, gens: &BpppGens) -> Result<(), ProofError> {
        gens.check_dims(self.n_lin, self.n_m)
    }

    /// The generators of this circuit ([`BpppGens::new`] with `n_lin`, `n_m`).
    pub fn gens<'a>(&self, pc: &PedersenGens, bp: &'a BulletproofGens) -> Result<BpppGens<'a>, ProofError> {
        BpppGens::new(pc, bp, self.n_lin, self.n_m)
    }

    /// The `BulletproofGens` capacity [`ArithmeticCircuit::gens`] needs.
    pub fn gens_capacity(&self) -> usize {
        BpppGens::capacity(self.n_lin, self.n_m)
    }

    /// The circuit digest absorbed by [`prove`] and [`CircuitProof::verify`] (spec §3.9).
    pub fn digest(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(b"bppp-circuit-digest v1");
        for x in self.dims() {
            h.update(x.to_le_bytes());
        }
        for &(slot, t) in &self.partition {
            h.update([slot as u8]);
            h.update((t as u64).to_le_bytes());
        }
        self.w_l.hash_into(&mut h);
        self.w_m.hash_into(&mut h);
        for a in self.a_l.iter().chain(&self.a_m) {
            h.update(a.as_bytes());
        }
        h.finalize().into()
    }

    /// Whether `w` satisfies the circuit (and both have the right shape).
    pub fn is_satisfied(&self, w: &CircuitWitness) -> bool {
        if self.check().is_err() || self.check_witness(w).is_err() {
            return false;
        }
        let full: Vec<Scalar> = w.w_l.iter().chain(&w.w_r).chain(&w.w_o).copied().collect();
        let w_v: Vec<Scalar> = w.v.iter().flatten().copied().collect();
        let pad = |r: usize| w_v.get(r).copied().unwrap_or(Scalar::ZERO);
        let lin = self.w_l.mul_vec(&full);
        let mul = self.w_m.mul_vec(&full);
        lin.iter().zip(&self.a_l).enumerate().all(|(r, (x, a))| x + flag(self.f_l) * pad(r) + a == Scalar::ZERO)
            && mul
                .iter()
                .zip(&self.a_m)
                .enumerate()
                .all(|(r, (x, a))| w.w_l[r] * w.w_r[r] == x + flag(self.f_m) * pad(r) + a)
    }
}

/// The challenge-dependent public vectors of spec §3.4, shared by prover and verifier.
struct Weights {
    mu_vec: Vec<Scalar>,
    c_nl: Vec<Scalar>,
    c_nr: Vec<Scalar>,
    c_no: Vec<Scalar>,
    c_lo: Vec<Scalar>,
    c_ll: Vec<Scalar>,
    c_lr: Vec<Scalar>,
    c_v: Vec<Scalar>,
    nu: Vec<Scalar>,
    /// `2 <mu, a_m> - 2 <Lambda, a_l>`.
    affine: Scalar,
}

impl Weights {
    fn new(c: &ArithmeticCircuit, rho: Scalar, lambda: Scalar) -> Self {
        let (n_m, n_lin) = (c.n_m, c.n_lin);
        let pw = |x: &Scalar, e: usize| util::scalar_exp_vartime(x, e as u64);
        let mu = rho * rho;
        let mu_vec = util::powers(mu, n_m + 1).split_off(1);
        let mu_inv_vec = util::powers(mu.invert(), n_m + 1).split_off(1);
        let mut lam = util::powers(lambda, c.n_l());
        if c.f_l && c.f_m {
            for i in 0..c.k {
                for j in 1..c.n_v {
                    let t = c.n_v * i + j;
                    lam[t] += pw(&mu, j) * pw(&lambda, c.n_v * i) - pw(&lambda, j) * pw(&mu, c.n_v * i + 1);
                }
            }
        }
        // y = Lambda^T W_l - mu^T W_m, one weight per column of w
        let mut y = vec![Scalar::ZERO; 2 * n_m + c.n_o];
        c.w_l.add_transposed(&lam, &mut y);
        c.w_m.add_transposed(&scaled(&mu_vec, -Scalar::ONE), &mut y);
        let c_nl = (0..n_m).map(|t| y[t] * mu_inv_vec[t]).collect();
        let c_nr = (0..n_m).map(|t| y[n_m + t] * mu_inv_vec[t]).collect();
        let mut c_no = vec![Scalar::ZERO; n_m];
        let (mut c_lo, mut c_ll, mut c_lr) = (vec![Scalar::ZERO; n_lin], vec![Scalar::ZERO; n_lin], vec![Scalar::ZERO; n_lin]);
        for (i, &(slot, t)) in c.partition.iter().enumerate() {
            let col = y[2 * n_m + i];
            match slot {
                Slot::NormO => c_no[t] = col * mu_inv_vec[t],
                Slot::LinO => c_lo[t] = col,
                Slot::LinL => c_ll[t] = col,
                Slot::LinR => c_lr[t] = col,
            }
        }
        let two = Scalar::from(2u64);
        let nu = (0..c.k)
            .map(|i| two * (flag(c.f_m) * pw(&mu, c.n_v * i + 1) - flag(c.f_l) * pw(&lambda, c.n_v * i)))
            .collect();
        let mut c_v = vec![Scalar::ZERO; n_lin];
        for j in 1..c.n_v {
            c_v[j - 1] = -(flag(c.f_m) * pw(&mu, j) + flag(c.f_l) * pw(&lambda, j));
        }
        let affine = two * ip(&mu_vec, &c.a_m) - two * ip(&lam, &c.a_l);
        Weights { mu_vec, c_nl, c_nr, c_no, c_lo, c_ll, c_lr, c_v, nu, affine }
    }

    /// `p_n(T) = delta^-1 T^3 c_nO + T^2 c_nL + T c_nR`.
    fn p_n(&self, delta_inv: Scalar) -> VecPoly {
        VecPoly(vec![(1, self.c_nr.clone()), (2, self.c_nl.clone()), (3, scaled(&self.c_no, delta_inv))])
    }

    /// `c_l(T) = 2 (delta^-1 T^3 c_lO + T^2 c_lL + T c_lR) + c_V`.
    fn c_l(&self, delta_inv: Scalar) -> VecPoly {
        let two = Scalar::from(2u64);
        VecPoly(vec![
            (0, self.c_v.clone()),
            (1, scaled(&self.c_lr, two)),
            (2, scaled(&self.c_ll, two)),
            (3, scaled(&self.c_lo, two * delta_inv)),
        ])
    }
}

fn c_r(beta: Scalar, tau: Scalar, tau_inv: Scalar) -> impl Iterator<Item = Scalar> {
    E_R.iter().map(move |&e| beta * pow_signed(tau, tau_inv, e))
}

/// `r_0 G + <r_{1..7} || l, H> + <n, N>` (constant time).
fn commit(gens: &BpppGens, r: &[Scalar; 8], l: &[Scalar], n: &[Scalar]) -> RistrettoPoint {
    let lin: Vec<Scalar> = r[1..].iter().chain(l).copied().collect();
    gens.g * r[0]
        + util::msm_slices(&lin, &gens.h, util::MSM_CHUNK_CT, false)
        + util::msm_slices(n, gens.n, util::MSM_CHUNK_CT, false)
}

/// Absorb the statement (spec §3.8); returns the circuit digest.
fn absorb_statement<T: BpppTranscript>(t: &mut T, c: &ArithmeticCircuit, gens: &BpppGens, V: &[CompressedRistretto]) -> [u8; 32] {
    t.domain_sep(b"bppp-circuit v1");
    let labels: [&'static [u8]; 8] = [b"N_m", b"N_O", b"N_v", b"N_lin", b"k", b"N_l", b"f_l", b"f_m"];
    for (label, x) in labels.iter().zip(c.dims()) {
        t.append_u64(label, x);
    }
    absorb_tail(t, gens, c.digest(), V)
}

/// The end of the statement of circuits and reciprocal form circuits (spec §3.8, §4.4): the
/// generators `G`, `H_0`, the circuit digest and the inputs; returns the digest. The value and
/// blinding generators may be application-specific (asset generators), so they are part of
/// the statement; the others are the fixed setup.
pub(crate) fn absorb_tail<T: BpppTranscript>(t: &mut T, gens: &BpppGens, digest: [u8; 32], V: &[CompressedRistretto]) -> [u8; 32] {
    t.append_point(b"G", &gens.g.compress());
    t.append_point(b"H_0", &gens.h[0].compress());
    t.append_message(b"circuit", &digest);
    for v in V {
        t.append_point(b"V", v);
    }
    digest
}

/// A challenge that must be invertible (zero has probability `2^-252`).
fn nonzero<T: BpppTranscript>(t: &mut T, label: &'static [u8]) -> Result<Scalar, ProofError> {
    let x = t.challenge(label);
    if x == Scalar::ZERO {
        Err(ProofError::VerificationError)
    } else {
        Ok(x)
    }
}

/// [`CircuitProof::prove`].
pub(crate) fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ArithmeticCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &CircuitWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    let secrets = w.w_l.iter().chain(&w.w_r).chain(&w.w_o).chain(w.v.iter().flatten()).chain(&w.s);
    prove_impl(c, gens, V, w, transcript, |t, digest| super::transcript::prover_rng(t, b"circuit", digest, secrets, rng), true)
}

/// The prover with the randomness `rng_for(transcript, digest)`, made once the statement is
/// absorbed: derived from the transcript by [`prove`], the caller's RNG as is in the tests.
fn prove_impl<T, R, F>(
    c: &ArithmeticCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &CircuitWitness,
    transcript: &mut T,
    rng_for: F,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError>
where
    T: BpppTranscript,
    R: RngCore + CryptoRng,
    F: FnOnce(&T, &[u8; 32]) -> R,
{
    // The generators bound the dimensions by memory that exists, so check them first.
    c.check_gens(gens)?;
    c.check()?;
    c.check_witness(w)?;
    if V.len() != c.k {
        return Err(ProofError::FormatError);
    }
    let digest = absorb_statement(transcript, c, gens, V);
    let rng = &mut rng_for(&*transcript, &digest);
    let o = commit_o(gens, c.n_lin, w.w_l.len(), &c.partition, &w.w_o, rng);
    let ol = commit_l(gens, o, &w.w_l, rng);
    let r = commit_r(gens, &ol, &w.w_r, rng);
    transcript.append_point(b"C_L", &ol.C_L);
    transcript.append_point(b"C_R", &r.C_R);
    transcript.append_point(b"C_O", &ol.o.C_O);
    prove_inner(c, gens, w, &ol, &r, transcript, rng, require_satisfied)
}

/// The prover's commitments to the initial witness (spec §3.3, CommitOL): `w_L` and the
/// `LinL` slots in `C_L`, the `NormO` and `LinO` slots in `C_O`.
pub(crate) struct CommittedOL {
    pub(crate) o: CommittedO,
    r_l: [Scalar; 8],
    pub C_L: CompressedRistretto,
}

impl CommittedOL {
    /// Set the `LinR` slots (committed later, in `C_R`) from `w_o`.
    pub(crate) fn set_late(&mut self, partition: &[(Slot, usize)], w_o: &[Scalar]) {
        for (x, &(slot, t)) in w_o.iter().zip(partition) {
            if slot == Slot::LinR {
                self.o.l_r[t] = *x;
            }
        }
    }
}

/// The zero patterns of the blinding vectors `r_O`, `r_L`, `r_R` (spec §3.3): with them the
/// blinding polynomial has no `T^3` term (spec §3.6). The non-zero entries are drawn in index
/// order.
const R_O: [bool; 8] = [true, true, true, true, false, true, true, false];
const R_L: [bool; 8] = [true, true, true, false, true, true, false, false];
const R_R: [bool; 8] = [true, true, false, true, true, false, false, false];

/// A blinding vector with the zero pattern `mask`.
fn draw_r<R: RngCore + CryptoRng>(rng: &mut R, mask: [bool; 8]) -> [Scalar; 8] {
    mask.map(|m| if m { Scalar::random(rng) } else { Scalar::ZERO })
}

/// The commitment to `w_R` and the `LinR` slots (spec §3.3, CommitR).
pub(crate) struct CommittedR {
    r_r: [Scalar; 8],
    pub C_R: CompressedRistretto,
}

/// The commitment to the early witness (spec §3.3 / §4.3): the `NormO` and `LinO` slots in
/// `C_O` (drawing `r'_O`), with the other slots of `w_O` set aside for `C_L` and `C_R`.
pub(crate) struct CommittedO {
    n_o: Vec<Scalar>,
    l_o: Vec<Scalar>,
    l_l: Vec<Scalar>,
    l_r: Vec<Scalar>,
    r_o: [Scalar; 8],
    pub C_O: CompressedRistretto,
}

/// CommitOL, first half: draws `r'_O` and commits `C_O`. `n_m` is the norm length.
pub(crate) fn commit_o<R: RngCore + CryptoRng>(
    gens: &BpppGens,
    n_lin: usize,
    n_m: usize,
    partition: &[(Slot, usize)],
    w_o: &[Scalar],
    rng: &mut R,
) -> CommittedO {
    let zero = Scalar::ZERO;
    let mut n_o = vec![zero; n_m];
    let (mut l_o, mut l_l, mut l_r) = (vec![zero; n_lin], vec![zero; n_lin], vec![zero; n_lin]);
    for (x, &(slot, t)) in w_o.iter().zip(partition) {
        match slot {
            Slot::NormO => n_o[t] = *x,
            Slot::LinO => l_o[t] = *x,
            Slot::LinL => l_l[t] = *x,
            Slot::LinR => l_r[t] = *x,
        }
    }
    let r_o = draw_r(rng, R_O);
    let C_O = commit(gens, &r_o, &l_o, &n_o).compress();
    CommittedO { n_o, l_o, l_l, l_r, r_o, C_O }
}

/// CommitOL, second half: draws `r'_L` and commits `C_L` (`w_l` and the `LinL` slots).
pub(crate) fn commit_l<R: RngCore + CryptoRng>(gens: &BpppGens, o: CommittedO, w_l: &[Scalar], rng: &mut R) -> CommittedOL {
    let r_l = draw_r(rng, R_L);
    let C_L = commit(gens, &r_l, &o.l_l, w_l).compress();
    CommittedOL { o, r_l, C_L }
}

/// CommitR: draws `r'_R` and commits `w_r` with the `LinR` slots.
pub(crate) fn commit_r<R: RngCore + CryptoRng>(
    gens: &BpppGens,
    ol: &CommittedOL,
    w_r: &[Scalar],
    rng: &mut R,
) -> CommittedR {
    let r_r = draw_r(rng, R_R);
    let C_R = commit(gens, &r_r, &ol.o.l_r, w_r).compress();
    CommittedR { r_r, C_R }
}

/// The inner protocol (spec §3.4–3.7), from the challenge `rho` on; the caller has absorbed
/// the statement and `C_L`, `C_R`, `C_O`. The witness and circuit must be checked.
pub(crate) fn prove_inner<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ArithmeticCircuit,
    gens: &BpppGens,
    w: &CircuitWitness,
    ol: &CommittedOL,
    cr: &CommittedR,
    transcript: &mut T,
    rng: &mut R,
    require_satisfied: bool,
) -> Result<CircuitProof, ProofError> {
    let (n_m, n_lin) = (c.n_m, c.n_lin);
    let zero = Scalar::ZERO;
    let (r_o, r_l, r_r) = (ol.o.r_o, ol.r_l, cr.r_r);
    let rho = nonzero(transcript, b"rho")?;
    let lambda = transcript.challenge(b"lambda");
    let beta = nonzero(transcript, b"beta")?;
    let delta = nonzero(transcript, b"delta")?;
    let wt = Weights::new(c, rho, lambda);
    let delta_inv = delta.invert();

    // Inputs (spec §3.4).
    let v_hat: Scalar = wt.nu.iter().zip(&w.v).map(|(nu, v)| nu * v[0]).sum();
    let mut l_v = vec![zero; n_lin];
    for (nu, v) in wt.nu.iter().zip(&w.v) {
        for (j, x) in v[1..].iter().enumerate() {
            l_v[j] += nu * x;
        }
    }
    let r_v = [zero, ip(&wt.nu, &w.s), zero, zero, zero, zero, zero, zero];
    let (l_s, n_s) = (draw(rng, n_lin), draw(rng, n_m));

    // Polynomials (spec §3.5).
    let p_n = wt.p_n(delta_inv);
    let n_t = VecPoly(vec![
        (-1, n_s.clone()),
        (0, scaled(&ol.o.n_o, delta)),
        (1, added(&w.w_l, &wt.c_nr)),
        (2, added(&w.w_r, &wt.c_nl)),
        (3, scaled(&wt.c_no, delta_inv)),
    ]);
    let l_hat = VecPoly(vec![
        (-1, l_s.clone()),
        (0, scaled(&ol.o.l_o, delta)),
        (1, ol.o.l_l.clone()),
        (2, ol.o.l_r.clone()),
        (3, l_v),
    ]);
    let c_l = wt.c_l(delta_inv);
    let mut f = p_n.inner(&p_n, Some(&wt.mu_vec));
    f.add(3, wt.affine + v_hat);
    f.sub_poly(&c_l.inner(&l_hat, None));
    f.sub_poly(&n_t.inner(&n_t, Some(&wt.mu_vec)));
    // f_3 = -2E vanishes exactly for a satisfying witness (w.h.p. over lambda, mu).
    if require_satisfied && f.coeff(3) != zero {
        return Err(ProofError::VerificationError);
    }

    // Blinding commitment (spec §3.6).
    let mut g = Poly::zero();
    for (r, deg, s) in [(&r_o, 0, delta), (&r_l, 1, Scalar::ONE), (&r_r, 2, Scalar::ONE), (&r_v, 3, Scalar::ONE)] {
        g.add(deg, -(s * r[0]));
        for (j, e) in E_R.iter().enumerate() {
            g.add(deg + e, beta * s * r[j + 1]);
        }
    }
    let mut d = f;
    d.sub_poly(&g);
    let beta_inv = beta.invert();
    let mut r_s = [zero; 8];
    r_s[0] = -d.coeff(-1);
    for (j, e) in E_R.iter().enumerate() {
        r_s[j + 1] = beta_inv * d.coeff(e - 1);
    }
    let C_S = commit(gens, &r_s, &l_s, &n_s).compress();
    transcript.append_point(b"C_S", &C_S);
    let tau = nonzero(transcript, b"tau")?;
    let tau_inv = tau.invert();

    // Norm argument on C(tau) (spec §3.7).
    let pw = |d: i32| pow_signed(tau, tau_inv, d);
    let r_tau = (0..8).map(|j| pw(-1) * r_s[j] + delta * r_o[j] + pw(1) * r_l[j] + pw(2) * r_r[j] + pw(3) * r_v[j]);
    let l: Vec<Scalar> = r_tau.skip(1).chain(l_hat.eval(tau, tau_inv, n_lin)).collect();
    let n = n_t.eval(tau, tau_inv, n_m);
    let cvec: Vec<Scalar> = c_r(beta, tau, tau_inv).chain(c_l.eval(tau, tau_inv, n_lin)).collect();
    let st = WnlaStatement { g: &gens.g, h: &gens.h, n: gens.n, c: &cvec, rho };
    let wnla = wnla::prove_unbound(&st, transcript, l, n, cfg!(feature = "bppp-vartime"))?;
    Ok(CircuitProof { C_L: ol.C_L, C_R: cr.C_R, C_O: ol.o.C_O, C_S, wnla })
}

impl CircuitProof {
    /// Prove that `w` satisfies `c` for the input commitments `V` (`V_i` =
    /// [`BpppGens::commit_input`]`(v_i, s_i)`). Absorbs the dimensions, the generators `G` and
    /// `H_0`, the circuit digest and `V` (spec §3.8). Returns `Err(VerificationError)` if the
    /// witness does not satisfy the circuit (the value term of spec §3.5 is non-zero).
    pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
        c: &ArithmeticCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        w: &CircuitWitness,
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<CircuitProof, ProofError> {
        prove(c, gens, V, w, transcript, rng)
    }

    /// Verify the proof for circuit `c` and input commitments `V`; absorbs the same statement
    /// as [`CircuitProof::prove`].
    pub fn verify<T: BpppTranscript>(
        &self,
        c: &ArithmeticCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        self.terms(c, gens, V, transcript)?.check(gens)
    }

    /// The terms of the verification equation (spec §3.7) of [`CircuitProof::verify`], for
    /// batch verification.
    pub(crate) fn terms<T: BpppTranscript>(
        &self,
        c: &ArithmeticCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<Terms, ProofError> {
        c.check_gens(gens)?;
        c.check().map_err(|_| ProofError::VerificationError)?;
        if V.len() != c.k {
            return Err(ProofError::VerificationError);
        }
        absorb_statement(transcript, c, gens, V);
        transcript.append_point(b"C_L", &self.C_L);
        transcript.append_point(b"C_R", &self.C_R);
        transcript.append_point(b"C_O", &self.C_O);
        self.inner_terms(c, V, transcript)
    }

    /// The terms of the inner verification (spec §3.7), from the challenge `rho` on; the caller
    /// has checked the shapes and absorbed the statement and `C_L`, `C_R`, `C_O`.
    pub(crate) fn inner_terms<T: BpppTranscript>(
        &self,
        c: &ArithmeticCircuit,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<Terms, ProofError> {
        let rho = nonzero(transcript, b"rho")?;
        let lambda = transcript.challenge(b"lambda");
        let beta = nonzero(transcript, b"beta")?;
        let delta = nonzero(transcript, b"delta")?;
        let wt = Weights::new(c, rho, lambda);
        let delta_inv = delta.invert();
        transcript.append_point(b"C_S", &self.C_S);
        let tau = nonzero(transcript, b"tau")?;
        let tau_inv = tau.invert();
        let tau3 = tau * tau * tau;

        let p_n = wt.p_n(delta_inv).eval(tau, tau_inv, c.n_m);
        let p_s = p_n.iter().zip(&p_n).zip(&wt.mu_vec).map(|((a, b), m)| a * b * m).sum::<Scalar>() + tau3 * wt.affine;
        let cvec: Vec<Scalar> = c_r(beta, tau, tau_inv).chain(wt.c_l(delta_inv).eval(tau, tau_inv, c.n_lin)).collect();
        let s = self.wnla.verification_scalars(&cvec, rho, c.n_m, transcript)?;

        let decompress = |p: &CompressedRistretto| p.decompress().ok_or(ProofError::VerificationError);
        let mut points = Vec::with_capacity(4 + V.len() + 2 * s.gammas.len());
        for (k, p) in [(-tau_inv, &self.C_S), (-delta, &self.C_O), (-tau, &self.C_L), (-(tau * tau), &self.C_R)] {
            points.push((k, decompress(p)?));
        }
        for (nu, v) in wt.nu.iter().zip(V) {
            points.push((-(tau3 * nu), decompress(v)?));
        }
        for ((g, X), R) in s.gammas.iter().zip(&self.wnla.X).zip(&self.wnla.R) {
            points.push((-g, decompress(X)?));
            points.push((Scalar::ONE - g * g, decompress(R)?));
        }
        let n: Vec<Scalar> = s.n.iter().zip(&p_n).map(|(a, b)| a - b).collect();
        Ok(Terms { g: s.g - p_s, h: s.h, n, points })
    }

    /// `C_L || C_R || C_O || C_S || norm argument` (spec §3.10).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for p in [&self.C_L, &self.C_R, &self.C_O, &self.C_S] {
            out.extend_from_slice(p.as_bytes());
        }
        out.extend(self.wnla.to_bytes());
        out
    }

    /// Parse a proof for circuit `c`.
    pub fn from_bytes(bytes: &[u8], c: &ArithmeticCircuit) -> Result<Self, ProofError> {
        Self::from_bytes_dims(bytes, c.n_lin, c.n_m)
    }

    /// Parse a proof for a linear part of length `n_lin` and `n_m` norm slots (the only
    /// dimensions the encoding depends on).
    pub(crate) fn from_bytes_dims(bytes: &[u8], n_lin: usize, n_m: usize) -> Result<Self, ProofError> {
        if bytes.len() < 128 {
            return Err(ProofError::FormatError);
        }
        let p = |i: usize| CompressedRistretto(util::read32(&bytes[32 * i..]));
        let a = n_lin.checked_add(H_FIXED).ok_or(ProofError::FormatError)?;
        let wnla = WnlaProof::from_bytes(&bytes[128..], a, n_m)?;
        Ok(CircuitProof { C_L: p(0), C_R: p(1), C_O: p(2), C_S: p(3), wnla })
    }
}

#[cfg(test)]
#[path = "circuit_tests.rs"]
mod tests;

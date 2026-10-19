//! Arithmetic circuit protocol (spec §3, paper §5).
//!
//! Proves `W_l w + f_l w_V + a_l = 0` and `w_L ∘ w_R = W_m w + f_m w_V + a_m` for a witness
//! `w = w_L || w_R || w_O` and committed input vectors `w_V`: commitments `C_L`, `C_R`, `C_O`,
//! challenges, a blinding commitment `C_S`, and one weighted norm linear argument.

use alloc::vec;
use alloc::vec::Vec;
use core::iter::once;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};
use rand_core::{CryptoRng, RngCore};
use sha3::{Digest, Sha3_256};

use super::gens::BpppGens;
use super::poly::{pow_signed, Poly, VecPoly};
use super::sparse::SparseMatrix;
use super::transcript::BpppTranscript;
use super::wnla::{self, WnlaProof, WnlaStatement};
use crate::errors::ProofError;
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

/// A witness for an [`ArithmeticCircuit`].
#[derive(Clone, Debug)]
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
        if self.partition.len() != self.n_o {
            return bad;
        }
        let mut used_n = vec![false; self.n_m];
        let mut used_l = vec![[false; 3]; self.n_lin];
        for &(slot, t) in &self.partition {
            let cell = match slot {
                Slot::NormO => used_n.get_mut(t),
                Slot::LinO => used_l.get_mut(t).map(|u| &mut u[0]),
                Slot::LinL => used_l.get_mut(t).map(|u| &mut u[1]),
                Slot::LinR => used_l.get_mut(t).map(|u| &mut u[2]),
            };
            match cell {
                Some(c) if !*c => *c = true,
                _ => return bad,
            }
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
        if gens.h.len() != self.n_lin + 7 || gens.n.len() != self.n_m {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        Ok(())
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

fn absorb_statement<T: BpppTranscript>(t: &mut T, c: &ArithmeticCircuit, V: &[CompressedRistretto], bind: bool) {
    t.domain_sep(b"bppp-circuit v1");
    let labels: [&'static [u8]; 8] = [b"N_m", b"N_O", b"N_v", b"N_lin", b"k", b"N_l", b"f_l", b"f_m"];
    for (label, x) in labels.iter().zip(c.dims()) {
        t.append_u64(label, x);
    }
    if bind {
        t.append_message(b"circuit", &c.digest());
    }
    for v in V {
        t.append_point(b"V", v);
    }
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

/// Prove that `w` satisfies `c` for the input commitments `V` (`V_i` =
/// [`BpppGens::commit_input`]`(v_i, s_i)`). Absorbs the dimensions, the circuit digest and
/// `V` (spec §3.8); an unsatisfied witness gives a proof that does not verify.
pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ArithmeticCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &CircuitWitness,
    transcript: &mut T,
    rng: &mut R,
) -> Result<CircuitProof, ProofError> {
    prove_impl(c, gens, V, w, transcript, rng, true)
}

fn prove_impl<T: BpppTranscript, R: RngCore + CryptoRng>(
    c: &ArithmeticCircuit,
    gens: &BpppGens,
    V: &[CompressedRistretto],
    w: &CircuitWitness,
    transcript: &mut T,
    rng: &mut R,
    bind: bool,
) -> Result<CircuitProof, ProofError> {
    c.check()?;
    c.check_witness(w)?;
    c.check_gens(gens)?;
    if V.len() != c.k {
        return Err(ProofError::FormatError);
    }
    let (n_m, n_lin) = (c.n_m, c.n_lin);
    let zero = Scalar::ZERO;

    // Commitments (spec §3.3).
    let mut n_o = vec![zero; n_m];
    let (mut l_o, mut l_l, mut l_r) = (vec![zero; n_lin], vec![zero; n_lin], vec![zero; n_lin]);
    for (x, &(slot, t)) in w.w_o.iter().zip(&c.partition) {
        match slot {
            Slot::NormO => n_o[t] = *x,
            Slot::LinO => l_o[t] = *x,
            Slot::LinL => l_l[t] = *x,
            Slot::LinR => l_r[t] = *x,
        }
    }
    let (ro, rl, rr) = (draw(rng, 6), draw(rng, 5), draw(rng, 4));
    let r_o = [ro[0], ro[1], ro[2], ro[3], zero, ro[4], ro[5], zero];
    let r_l = [rl[0], rl[1], rl[2], zero, rl[3], rl[4], zero, zero];
    let r_r = [rr[0], rr[1], zero, rr[2], rr[3], zero, zero, zero];
    let C_L = commit(gens, &r_l, &l_l, &w.w_l).compress();
    let C_R = commit(gens, &r_r, &l_r, &w.w_r).compress();
    let C_O = commit(gens, &r_o, &l_o, &n_o).compress();

    absorb_statement(transcript, c, V, bind);
    transcript.append_point(b"C_L", &C_L);
    transcript.append_point(b"C_R", &C_R);
    transcript.append_point(b"C_O", &C_O);
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
        (0, scaled(&n_o, delta)),
        (1, added(&w.w_l, &wt.c_nr)),
        (2, added(&w.w_r, &wt.c_nl)),
        (3, scaled(&wt.c_no, delta_inv)),
    ]);
    let l_hat = VecPoly(vec![(-1, l_s.clone()), (0, scaled(&l_o, delta)), (1, l_l), (2, l_r), (3, l_v)]);
    let c_l = wt.c_l(delta_inv);
    let mut f = p_n.inner(&p_n, Some(&wt.mu_vec));
    f.add(3, wt.affine + v_hat);
    f.sub_poly(&c_l.inner(&l_hat, None));
    f.sub_poly(&n_t.inner(&n_t, Some(&wt.mu_vec)));

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
    let st = WnlaStatement { g: &gens.g, h_vec: &gens.h, n_vec: gens.n, c: &cvec, rho };
    let wnla = wnla::prove_unbound(&st, transcript, l, n)?;
    Ok(CircuitProof { C_L, C_R, C_O, C_S, wnla })
}

impl CircuitProof {
    /// Verify the proof for circuit `c` and input commitments `V`; absorbs the same statement
    /// as [`prove`].
    pub fn verify<T: BpppTranscript>(
        &self,
        c: &ArithmeticCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_impl(c, gens, V, transcript, true)
    }

    fn verify_impl<T: BpppTranscript>(
        &self,
        c: &ArithmeticCircuit,
        gens: &BpppGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
        bind: bool,
    ) -> Result<(), ProofError> {
        c.check().map_err(|_| ProofError::VerificationError)?;
        c.check_gens(gens)?;
        if V.len() != c.k {
            return Err(ProofError::VerificationError);
        }
        absorb_statement(transcript, c, V, bind);
        transcript.append_point(b"C_L", &self.C_L);
        transcript.append_point(b"C_R", &self.C_R);
        transcript.append_point(b"C_O", &self.C_O);
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
        let comms = [self.C_S, self.C_O, self.C_L, self.C_R].iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let inputs = V.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let xs = self.wnla.X.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let rs = self.wnla.R.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let small = RistrettoPoint::vartime_multiscalar_mul(
            once(s.g - p_s)
                .chain([-tau_inv, -delta, -tau, -(tau * tau)])
                .chain(wt.nu.iter().map(|nu| -(tau3 * nu)))
                .chain(s.gammas.iter().map(|g| -g))
                .chain(s.gammas.iter().map(|g| Scalar::ONE - g * g)),
            once(&gens.g).chain(comms.iter()).chain(inputs.iter()).chain(xs.iter()).chain(rs.iter()),
        );
        let n_coef: Vec<Scalar> = s.n.iter().zip(&p_n).map(|(a, b)| a - b).collect();
        let check = small
            + util::vartime_msm_slices(&s.h, &gens.h, util::MSM_CHUNK_VT)
            + util::vartime_msm_slices(&n_coef, gens.n, util::MSM_CHUNK_VT);
        if check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
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
        if bytes.len() < 128 {
            return Err(ProofError::FormatError);
        }
        let p = |i: usize| CompressedRistretto(util::read32(&bytes[32 * i..]));
        let a = c.n_lin.checked_add(7).ok_or(ProofError::FormatError)?;
        let wnla = WnlaProof::from_bytes(&bytes[128..], a, c.n_m)?;
        Ok(CircuitProof { C_L: p(0), C_R: p(1), C_O: p(2), C_S: p(3), wnla })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bppp::transcript::Replay;
    use crate::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    struct Shape {
        n_m: usize,
        n_o: usize,
        n_v: usize,
        n_lin: usize,
        k: usize,
        n_l: usize,
        f_l: bool,
        f_m: bool,
        spread: bool,
    }

    fn rand_vec(rng: &mut ChaCha20Rng, n: usize) -> Vec<Scalar> {
        (0..n).map(|_| Scalar::random(rng)).collect()
    }

    fn sparse(rng: &mut ChaCha20Rng, rows: usize, cols: usize) -> SparseMatrix {
        use rand_chacha::rand_core::RngCore;
        let mut m = SparseMatrix::new(cols);
        for _ in 0..rows {
            let mut terms = Vec::new();
            for c in 0..cols {
                if rng.next_u32() % 2 == 0 {
                    terms.push((c, Scalar::random(rng)));
                }
            }
            m.push_row(terms);
        }
        m
    }

    /// A random circuit with a satisfying witness: `W_l`, `W_m` and the witness are random,
    /// `a_l` and `a_m` are chosen to satisfy the circuit.
    fn instance(rng: &mut ChaCha20Rng, s: &Shape) -> (ArithmeticCircuit, CircuitWitness) {
        let n_w = 2 * s.n_m + s.n_o;
        let w = CircuitWitness {
            w_l: rand_vec(rng, s.n_m),
            w_r: rand_vec(rng, s.n_m),
            w_o: rand_vec(rng, s.n_o),
            v: (0..s.k).map(|_| rand_vec(rng, s.n_v)).collect(),
            s: rand_vec(rng, s.k),
        };
        let w_l = sparse(rng, s.n_l, n_w);
        let w_m = sparse(rng, s.n_m, n_w);
        let full: Vec<Scalar> = w.w_l.iter().chain(&w.w_r).chain(&w.w_o).copied().collect();
        let w_v: Vec<Scalar> = w.v.iter().flatten().copied().collect();
        let pad = |r: usize| w_v.get(r).copied().unwrap_or(Scalar::ZERO);
        let flag = |f: bool| if f { Scalar::ONE } else { Scalar::ZERO };
        let a_l = w_l.mul_vec(&full).iter().enumerate().map(|(r, x)| -(x + flag(s.f_l) * pad(r))).collect();
        let a_m = w_m
            .mul_vec(&full)
            .iter()
            .enumerate()
            .map(|(r, x)| w.w_l[r] * w.w_r[r] - x - flag(s.f_m) * pad(r))
            .collect();
        let slots = [Slot::NormO, Slot::LinO, Slot::LinL, Slot::LinR];
        let partition =
            (0..s.n_o).map(|i| if s.spread { (slots[i % 4], i / 4) } else { (Slot::NormO, i) }).collect();
        let c = ArithmeticCircuit {
            n_m: s.n_m,
            n_o: s.n_o,
            n_v: s.n_v,
            n_lin: s.n_lin,
            k: s.k,
            w_l,
            a_l,
            w_m,
            a_m,
            f_l: s.f_l,
            f_m: s.f_m,
            partition,
        };
        (c, w)
    }

    fn shapes() -> Vec<Shape> {
        let mut out = Vec::new();
        for &(f_l, f_m) in &[(false, false), (true, false), (false, true), (true, true)] {
            for &k in &[1, 3] {
                for &n_v in &[1, 4] {
                    for &spread in &[false, true] {
                        out.push(Shape {
                            n_m: 16,
                            n_o: 8,
                            n_v,
                            n_lin: (n_v - 1).max(4),
                            k,
                            n_l: (k * n_v).max(5) + 2,
                            f_l,
                            f_m,
                            spread,
                        });
                    }
                }
            }
        }
        out.push(Shape { n_m: 1, n_o: 0, n_v: 1, n_lin: 0, k: 1, n_l: 1, f_l: true, f_m: true, spread: false });
        out.push(Shape { n_m: 5, n_o: 3, n_v: 3, n_lin: 2, k: 1, n_l: 4, f_l: true, f_m: false, spread: false });
        out
    }

    fn gens_for(c: &ArithmeticCircuit) -> (PedersenGens, BulletproofGens) {
        (PedersenGens::default(), BulletproofGens::new(c.n_m.max(c.n_lin + 6), 1))
    }

    fn commitments(g: &BpppGens, w: &CircuitWitness) -> Vec<CompressedRistretto> {
        w.v.iter().zip(&w.s).map(|(v, s)| g.commit_input(v, *s).compress()).collect()
    }

    fn prove_and_verify(c: &ArithmeticCircuit, w: &CircuitWitness, rng: &mut ChaCha20Rng) -> Result<(), ProofError> {
        let (pc, bp) = gens_for(c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m)?;
        let V = commitments(&g, w);
        let proof = prove(c, &g, &V, w, &mut Transcript::new(b"test"), rng)?;
        let parsed = CircuitProof::from_bytes(&proof.to_bytes(), c)?;
        assert_eq!(parsed, proof);
        proof.verify(c, &g, &V, &mut Transcript::new(b"test"))
    }

    /// Hands out the given scalars to `Scalar::random` (32 bytes little-endian, then 32 zero
    /// bytes: the wide reduction returns the scalar itself).
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

    /// The prover reproduces the independent Python reference (`ref/bppp_ref.py`,
    /// `tests/vectors/bppp/circuit.json`) given its randomness and challenges, and the
    /// verifier accepts exactly the satisfied cases.
    #[test]
    fn matches_reference_vectors() {
        let file: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/bppp/circuit.json")).unwrap();
        let pc = PedersenGens::default();
        for case in file["cases"].as_array().unwrap() {
            let name = case["name"].as_str().unwrap();
            let u = |k: &str| case[k].as_u64().unwrap() as usize;
            let (n_m, n_o, n_lin) = (u("n_m"), u("n_o"), u("n_lin"));
            let n_w = 2 * n_m + n_o;
            let slot = |s: &str| match s {
                "nO" => Slot::NormO,
                "lO" => Slot::LinO,
                "lL" => Slot::LinL,
                "lR" => Slot::LinR,
                _ => panic!("slot {}", s),
            };
            let c = ArithmeticCircuit {
                n_m,
                n_o,
                n_v: u("n_v"),
                n_lin,
                k: u("k"),
                w_l: sparse_from(&case["w_l"], n_w),
                a_l: scs(&case["a_l"]),
                w_m: sparse_from(&case["w_m"], n_w),
                a_m: scs(&case["a_m"]),
                f_l: u("f_l") == 1,
                f_m: u("f_m") == 1,
                partition: case["partition"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|p| (slot(p[0].as_str().unwrap()), p[1].as_u64().unwrap() as usize))
                    .collect(),
            };
            assert_eq!(c.n_l(), u("n_l"), "{}", name);
            let w = CircuitWitness {
                w_l: scs(&case["w_L"]),
                w_r: scs(&case["w_R"]),
                w_o: scs(&case["w_O"]),
                v: case["v"].as_array().unwrap().iter().map(scs).collect(),
                s: scs(&case["s"]),
            };
            assert_eq!(c.is_satisfied(&w), case["satisfied"].as_bool().unwrap(), "{}", name);
            let bp = BulletproofGens::new(n_m.max(n_lin + 6), 1);
            let g = BpppGens::new(&pc, &bp, n_lin, n_m).unwrap();
            let point = |p: &serde_json::Value| {
                use curve25519_dalek::traits::MultiscalarMul;
                (g.g * sc(&p["g"])
                    + RistrettoPoint::multiscalar_mul(scs(&p["h"]), &g.h)
                    + RistrettoPoint::multiscalar_mul(scs(&p["n"]), g.n))
                .compress()
            };
            let V: Vec<CompressedRistretto> = w.v.iter().zip(&w.s).map(|(v, s)| g.commit_input(v, *s).compress()).collect();
            for (i, p) in case["V"].as_array().unwrap().iter().enumerate() {
                assert_eq!(V[i], point(p), "{}: V_{}", name, i);
            }
            let r = &case["rand"];
            let randomness: Vec<Scalar> =
                ["r_O", "r_L", "r_R", "l_S", "n_S"].iter().flat_map(|k| scs(&r[*k])).collect();
            let ch = &case["chal"];
            let challenges: Vec<Scalar> = ["rho", "lambda", "beta", "delta", "tau"]
                .iter()
                .map(|k| sc(&ch[*k]))
                .chain(scs(&case["gammas"]))
                .collect();
            let proof =
                prove(&c, &g, &V, &w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness)).unwrap();
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
            let verdict = proof.verify(&c, &g, &V, &mut Replay::new(challenges)).is_ok();
            assert_eq!(verdict, case["verifies"].as_bool().unwrap(), "{}: verdict", name);
        }
    }

    #[test]
    fn honest_proofs_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(10);
        for s in shapes() {
            let (c, w) = instance(&mut rng, &s);
            assert!(c.is_satisfied(&w));
            let res = prove_and_verify(&c, &w, &mut rng);
            assert!(res.is_ok(), "f_l={} f_m={} k={} n_v={} spread={}: {:?}", s.f_l, s.f_m, s.k, s.n_v, s.spread, res);
        }
    }

    /// Each kind of violated constraint makes the proof fail: a linear one, a multiplicative
    /// one, and one through an input value.
    #[test]
    fn unsatisfied_witnesses_are_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        for s in shapes().into_iter().filter(|s| s.n_m > 1) {
            for tamper in 0..4 {
                let (mut c, mut w) = instance(&mut rng, &s);
                match tamper {
                    0 => c.a_l[0] += Scalar::ONE,
                    1 => *c.a_m.last_mut().unwrap() += Scalar::ONE,
                    2 => w.w_l[0] += Scalar::ONE,
                    _ if s.f_l || s.f_m => *w.v[s.k - 1].last_mut().unwrap() += Scalar::ONE,
                    _ => continue,
                }
                if c.is_satisfied(&w) {
                    continue; // the tampered entry happened to be unconstrained
                }
                assert!(prove_and_verify(&c, &w, &mut rng).is_err(), "tamper {} accepted", tamper);
            }
        }
    }

    #[test]
    fn scalar_inputs_are_pedersen_commitments() {
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(16, 1);
        let g = BpppGens::new(&pc, &bp, 3, 16).unwrap();
        let (v, s) = (Scalar::from(1234u64), Scalar::from(99u64));
        assert_eq!(g.commit_input(&[v], s), pc.commit(v, s));
    }

    /// The transcript carries the dimensions, the circuit digest, the inputs and every
    /// commitment before the challenges that depend on them; the verifier absorbs the same.
    #[test]
    fn transcript_binds_messages() {
        let mut rng = ChaCha20Rng::seed_from_u64(12);
        let s = Shape { n_m: 4, n_o: 2, n_v: 2, n_lin: 2, k: 2, n_l: 5, f_l: true, f_m: true, spread: true };
        let (c, w) = instance(&mut rng, &s);
        let (pc, bp) = gens_for(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
        let V = commitments(&g, &w);
        let chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
        let mut t = Replay::new(chal.clone());
        let proof = prove(&c, &g, &V, &w, &mut t, &mut rng).unwrap();
        let u = |x: u64| x.to_le_bytes().to_vec();
        let mut expected: Vec<(&[u8], Vec<u8>)> = vec![
            (b"bppp-circuit v1", vec![]),
            (b"N_m", u(4)),
            (b"N_O", u(2)),
            (b"N_v", u(2)),
            (b"N_lin", u(2)),
            (b"k", u(2)),
            (b"N_l", u(5)),
            (b"f_l", u(1)),
            (b"f_m", u(1)),
            (b"circuit", c.digest().to_vec()),
            (b"V", V[0].as_bytes().to_vec()),
            (b"V", V[1].as_bytes().to_vec()),
            (b"C_L", proof.C_L.as_bytes().to_vec()),
            (b"C_R", proof.C_R.as_bytes().to_vec()),
            (b"C_O", proof.C_O.as_bytes().to_vec()),
            (b"rho", vec![]),
            (b"lambda", vec![]),
            (b"beta", vec![]),
            (b"delta", vec![]),
            (b"C_S", proof.C_S.as_bytes().to_vec()),
            (b"tau", vec![]),
        ];
        let header = expected.len();
        assert_eq!(&t.log[..header], &expected[..], "prover");
        assert_eq!(t.log[header].0, &b"bppp-wnla v1"[..]);
        expected = t.log.clone();
        let mut tv = Replay::new(chal);
        proof.verify(&c, &g, &V, &mut tv).unwrap();
        assert_eq!(tv.log, expected, "verifier");
    }

    #[test]
    fn digest_changes_with_every_part_of_the_circuit() {
        let mut rng = ChaCha20Rng::seed_from_u64(13);
        let s = Shape { n_m: 4, n_o: 4, n_v: 2, n_lin: 2, k: 1, n_l: 3, f_l: true, f_m: false, spread: true };
        let (c, _) = instance(&mut rng, &s);
        let d = c.digest();
        let mut variants = Vec::new();
        let mut x = c.clone();
        x.a_l[1] += Scalar::ONE;
        variants.push(x);
        let mut x = c.clone();
        x.a_m[0] += Scalar::ONE;
        variants.push(x);
        let mut x = c.clone();
        x.f_m = true;
        variants.push(x);
        let mut x = c.clone();
        x.partition.swap(0, 1);
        variants.push(x);
        let mut x = c.clone();
        x.w_l.push_row(vec![(0, Scalar::ONE)]);
        x.a_l.push(Scalar::ZERO);
        variants.push(x);
        for v in variants {
            assert_ne!(v.digest(), d);
        }
    }

    #[test]
    fn degenerate_challenges_fail() {
        let mut rng = ChaCha20Rng::seed_from_u64(14);
        let s = Shape { n_m: 4, n_o: 2, n_v: 1, n_lin: 1, k: 1, n_l: 2, f_l: true, f_m: false, spread: false };
        let (c, w) = instance(&mut rng, &s);
        let (pc, bp) = gens_for(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
        let V = commitments(&g, &w);
        // challenge order: rho, lambda, beta, delta, tau, gammas...
        for zero in [0usize, 2, 3, 4] {
            let mut chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
            chal[zero] = Scalar::ZERO;
            assert!(prove(&c, &g, &V, &w, &mut Replay::new(chal), &mut rng).is_err(), "challenge {} zero", zero);
        }
        let good: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
        let proof = prove(&c, &g, &V, &w, &mut Replay::new(good.clone()), &mut rng).unwrap();
        proof.verify(&c, &g, &V, &mut Replay::new(good)).unwrap();
        for zero in [0usize, 2, 3, 4] {
            let mut chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
            chal[zero] = Scalar::ZERO;
            assert!(proof.verify(&c, &g, &V, &mut Replay::new(chal)).is_err(), "challenge {} zero", zero);
        }
    }

    #[test]
    fn malformed_inputs_are_errors() {
        let mut rng = ChaCha20Rng::seed_from_u64(15);
        let s = Shape { n_m: 4, n_o: 2, n_v: 2, n_lin: 2, k: 2, n_l: 5, f_l: true, f_m: false, spread: true };
        let (c, w) = instance(&mut rng, &s);
        let (pc, bp) = gens_for(&c);
        let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
        let V = commitments(&g, &w);
        let proof = prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).unwrap();
        let bytes = proof.to_bytes();
        assert!(CircuitProof::from_bytes(&bytes[1..], &c).is_err());
        assert!(CircuitProof::from_bytes(&[], &c).is_err());
        let ok = |p: &CircuitProof, V: &[CompressedRistretto]| p.verify(&c, &g, V, &mut Transcript::new(b"t")).is_ok();
        assert!(ok(&proof, &V));
        assert!(!ok(&proof, &V[..1]), "missing input");
        let mut swapped = V.clone();
        swapped.swap(0, 1);
        assert!(!ok(&proof, &swapped), "inputs swapped");
        let mut bad = proof.clone();
        bad.C_S = CompressedRistretto([0xff; 32]);
        assert!(!ok(&bad, &V), "invalid point");
        let mut bad = proof.clone();
        bad.C_O = proof.C_L;
        assert!(!ok(&bad, &V), "C_O replaced");
        // shape errors are errors, not panics
        let mut c2 = c.clone();
        c2.partition.push((Slot::NormO, 0));
        assert!(prove(&c2, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).is_err());
        let mut c3 = c.clone();
        c3.partition[0] = c3.partition[1];
        assert!(c3.check().is_err(), "partition not injective");
        let small = BulletproofGens::new(2, 1);
        assert!(BpppGens::new(&pc, &small, c.n_lin, c.n_m).is_err());
    }
}

//! Weighted norm linear argument (spec §2, paper §4).
//!
//! Proves knowledge of `l`, `n` with `C = v*G + <l, H> + <n, N>` and
//! `v = <c, l> + |n|^2_mu`, `mu = rho^2`, for public `c` and `rho`. Vectors are split into
//! even and odd components and folded while a round removes at least three scalars; the rest
//! is sent in the clear. Algebra, length-1 rule and layout follow secp256k1-zkp (spec §2).
//!
//! The argument is **not zero-knowledge**: the final vectors are combinations of the witness.
//! Hiding comes from the blinding of the circuit protocol built on top of it. [`prove`] and
//! [`WnlaProof::verify`] absorb `G`, `C`, `rho` and `c` (spec §2.3); the vector generators are
//! the setup.

use alloc::vec;
use alloc::vec::Vec;
use core::iter::once;


use ff::Field as _;

use super::terms::Terms;
use super::transcript::BpppTranscript;
use crate::curve::{Curve, Field, PointEncoding, Ristretto};
use crate::errors::ProofError;
use crate::util;

/// Public input of the argument. `h_vec` and `c` have the length of `l`, `n_vec` that of `n`.
pub struct WnlaStatement<'a, C: Curve = Ristretto> {
    /// Value generator `G`.
    pub g: &'a C::Point,
    /// Generators of the linear part `l`.
    pub h: &'a [C::Point],
    /// Generators of the norm part `n`.
    pub n: &'a [C::Point],
    /// Linear constraint vector.
    pub c: &'a [C::Scalar],
    /// Square root of the norm weight, `mu = rho^2`; non-zero.
    pub rho: C::Scalar,
}

/// A WNLA proof: one `(X, R)` pair per round and the final vectors.
#[derive(Clone, Debug, PartialEq)]
pub struct WnlaProof<C: Curve = Ristretto> {
    /// `X_r`, the `gamma` coefficients.
    pub X: Vec<C::Compressed>,
    /// `R_r`, the `gamma^2 - 1` coefficients.
    pub R: Vec<C::Compressed>,
    /// Final `l`.
    pub l: Vec<C::Scalar>,
    /// Final `n`.
    pub n: Vec<C::Scalar>,
}

/// Scalars of the verification equation (spec §2.4):
/// `g*G + <h, H> + <n, N> - C - sum_r (gamma_r X_r + (gamma_r^2 - 1) R_r) = 0`.
/// The circuit verifier merges them into its own multiscalar multiplication.
pub struct WnlaScalars<F: Field = curve25519_dalek::scalar::Scalar> {
    /// Coefficient of `G` (the value `v` of the final vectors).
    pub g: F,
    /// Coefficients of `H`.
    pub h: Vec<F>,
    /// Coefficients of `N`.
    pub n: Vec<F>,
    /// The round challenges.
    pub gammas: Vec<F>,
}

/// Whether one more round pays off: it costs two points and removes `a/2 + b/2` scalars
/// (spec §2.2, the optimal layout of secp256k1-zkp PR #352).
fn more(a: usize, b: usize) -> bool {
    a / 2 + b / 2 >= 3
}

/// `(rounds, final |l|, final |n|)` for `|l| = a`, `|n| = b`.
pub fn rounds(mut a: usize, mut b: usize) -> (usize, usize, usize) {
    let mut k = 0;
    while more(a, b) {
        a -= a / 2; // ceil(a / 2) without overflow
        b -= b / 2;
        k += 1;
    }
    (k, a, b)
}

fn ip<F: Field>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b).map(|(x, y)| *x * y).sum()
}

/// `<a, b>_mu = sum_i a_i b_i mu^(i+1)`.
fn wip<F: Field>(a: &[F], b: &[F], mu: F) -> F {
    let mut w = mu;
    let mut acc = F::ZERO;
    for (x, y) in a.iter().zip(b) {
        acc += *x * y * w;
        w *= mu;
    }
    acc
}

/// `e*[v]_0 + g*[v]_1`, zero-padded on the right: length `ceil(|v|/2)`.
fn fold<F: Field>(v: &[F], e: F, g: F) -> Vec<F> {
    util::map_index((v.len() + 1) / 2, |i| {
        e * v[2 * i] + v.get(2 * i + 1).map_or(F::ZERO, |x| g * x)
    })
}

/// `P_{2i} + g P_{2i+1}` (an unpaired last point stays): generators, public scalars.
fn fold_points<C: Curve>(p: &[C::Point], g: C::Scalar) -> Vec<C::Point> {
    util::map_index((p.len() + 1) / 2, |i| match p.get(2 * i + 1) {
        Some(hi) => p[2 * i] + *hi * g,
        None => p[2 * i],
    })
}

/// Constant-time `sum_i s_i P_i` over the common prefix (implicit zero padding).
fn ct_msm<C: Curve>(s: &[C::Scalar], p: &[C::Point]) -> C::Point {
    let m = s.len().min(p.len());
    C::msm_ct(&s[..m], &p[..m])
}

impl<C: Curve> WnlaStatement<'_, C> {
    fn check(&self, a: usize, b: usize) -> Result<(), ProofError> {
        if self.h.len() != a || self.c.len() != a || self.n.len() != b {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if self.rho == C::Scalar::ZERO {
            return Err(ProofError::FormatError);
        }
        Ok(())
    }

    /// `v*G + <l, H> + <n, N>` with `v = <c, l> + |n|^2_mu` (constant time).
    pub fn commit(&self, l: &[C::Scalar], n: &[C::Scalar]) -> C::Point {
        let v = ip(self.c, l) + wip(n, n, self.rho * self.rho);
        *self.g * v + ct_msm::<C>(l, self.h) + ct_msm::<C>(n, self.n)
    }
}

fn absorb_header<C: Curve, T: BpppTranscript + ?Sized>(transcript: &mut T, a: usize, b: usize) {
    transcript.domain_sep(b"bppp-wnla v1");
    transcript.curve_domain_sep::<C>();
    transcript.append_u64(b"l", a as u64);
    transcript.append_u64(b"n", b as u64);
}

/// Absorb the public input of a standalone argument (spec §2.3).
fn absorb_statement<C: Curve, T: BpppTranscript + ?Sized>(transcript: &mut T, st: &WnlaStatement<C>, com: &C::Compressed) {
    transcript.domain_sep(b"bppp-wnla-statement v1");
    transcript.append_point(b"G", &C::compress(st.g));
    transcript.append_point(b"C", com);
    transcript.append_scalar(b"rho", &st.rho);
    st.c.iter().for_each(|c| transcript.append_scalar(b"c", c));
}

/// [`WnlaProof::prove`].
pub(crate) fn prove<C: Curve, T: BpppTranscript + ?Sized>(
    st: &WnlaStatement<C>,
    com: &C::Point,
    transcript: &mut T,
    l: Vec<C::Scalar>,
    n: Vec<C::Scalar>,
) -> Result<WnlaProof<C>, ProofError> {
    st.check(l.len(), n.len())?;
    absorb_statement(transcript, st, &C::compress(com));
    prove_unbound(st, transcript, l, n, false)
}

/// [`prove`] without absorbing the statement, for the circuit protocol: there `C`, `c` and
/// `rho` are functions of commitments and challenges already in the transcript, and
/// computing `C` explicitly would cost a full multiscalar multiplication. `vartime` computes
/// the round commitments in variable time (only for inputs that are uniformly random given
/// the transcript, spec §2.6).
pub(crate) fn prove_unbound<C: Curve, T: BpppTranscript + ?Sized>(
    st: &WnlaStatement<C>,
    transcript: &mut T,
    l: Vec<C::Scalar>,
    n: Vec<C::Scalar>,
    vartime: bool,
) -> Result<WnlaProof<C>, ProofError> {
    prove_rounds(st, transcript, l, n, vartime, if vartime { DEFERRED_VT } else { DEFERRED_CT })
}

/// Rounds that compute `X`, `R` from the input generators instead of folding them: a fold
/// costs about 2.5 constant-time or 8 variable-time multiscalar terms, a deferred round
/// `1.5 b` terms instead of `1.5 b / 2^r` (measured best: 2 and 3).
const DEFERRED_CT: usize = 2;
const DEFERRED_VT: usize = 3;

/// The generators of one vector after `r` deferred rounds: folded generator `i` is
/// `scale * sum_t coef[t] P[i 2^r + t]` (missing indices are the identity).
struct Deferred<'a, C: Curve> {
    input: &'a [C::Point],
    folded: Option<Vec<C::Point>>,
    /// `2^r` coefficients while deferred.
    coef: Vec<C::Scalar>,
    shift: u32,
}

impl<'a, C: Curve> Deferred<'a, C> {
    fn new(input: &'a [C::Point]) -> Self {
        Deferred { input, folded: None, coef: vec![C::Scalar::ONE], shift: 0 }
    }

    /// Current length of the folded vector.
    fn len(&self) -> usize {
        match &self.folded {
            Some(f) => f.len(),
            None => (self.input.len() + (1 << self.shift) - 1) >> self.shift,
        }
    }

    /// The terms of `sum_j x_j P'_j` over the current generators, all positions `j` or only
    /// the odd ones: their number and, for a term index, `(j, k, P)` meaning `x_j k P` (a
    /// padding term has `k = 0`).
    fn terms<'s>(&'s self, odd_only: bool) -> (usize, Box<dyn Fn(usize) -> (usize, C::Scalar, &'s C::Point) + Sync + 's>) {
        match (&self.folded, odd_only) {
            (Some(f), false) => (f.len(), Box::new(move |v| (v, C::Scalar::ONE, &f[v]))),
            (Some(f), true) => (f.len() / 2, Box::new(move |i| (2 * i + 1, C::Scalar::ONE, &f[2 * i + 1]))),
            (None, false) => {
                let mask = (1usize << self.shift) - 1;
                (self.input.len(), Box::new(move |v| (v >> self.shift, self.coef[v & mask], &self.input[v])))
            }
            (None, true) => {
                let (shift, mask) = (self.shift, (1usize << self.shift) - 1);
                let count = (self.len() / 2) << shift;
                (
                    count,
                    Box::new(move |i| {
                        let (j, t) = (2 * (i >> shift) + 1, i & mask);
                        let v = (j << shift) + t;
                        match self.input.get(v) {
                            Some(p) => (j, self.coef[t], p),
                            None => (j, C::Scalar::ZERO, &self.input[0]),
                        }
                    }),
                )
            }
        }
    }

    /// Fold: `P'_i = P_{2i} + g P_{2i+1}`; materialise after `defer` rounds.
    fn fold(&mut self, g: C::Scalar, defer: usize) {
        match &self.folded {
            Some(f) => self.folded = Some(fold_points::<C>(f, g)),
            None => {
                self.coef = self.coef.iter().copied().chain(self.coef.iter().map(|c| *c * g)).collect();
                self.shift += 1;
                // materialise after `defer` rounds, or when the vector stops folding (length 1)
                if self.shift as usize >= defer || self.len() <= 1 {
                    let (rows, input, coef, shift) = (1usize << self.shift, self.input, &self.coef, self.shift);
                    let m = self.len();
                    self.folded = Some(util::map_index(m, |i| {
                        let lo = i << shift;
                        let hi = (lo + rows).min(input.len());
                        C::msm_vt(&coef[..hi - lo], &input[lo..hi])
                    }));
                }
            }
        }
    }
}

fn prove_rounds<C: Curve, T: BpppTranscript + ?Sized>(
    st: &WnlaStatement<C>,
    transcript: &mut T,
    l: Vec<C::Scalar>,
    n: Vec<C::Scalar>,
    vartime: bool,
    defer: usize,
) -> Result<WnlaProof<C>, ProofError> {
    st.check(l.len(), n.len())?;
    absorb_header::<C, T>(transcript, l.len(), n.len());
    let (mut l, mut n, mut c) = (l, n, st.c.to_vec());
    // The folded generators: `H` as they are, `N` as `s * N'` (so that folding `N` costs one
    // scalar multiplication per pair, as for `H`); the inputs are not copied.
    let mut h = Deferred::<C>::new(st.h);
    let mut g = Deferred::<C>::new(st.n);
    let mut s = C::Scalar::ONE;
    let (mut rho, mut mu) = (st.rho, st.rho * st.rho);
    let (mut xs, mut rs) = (Vec::new(), Vec::new());
    while more(l.len(), n.len()) {
        let (a, b) = (l.len(), n.len());
        debug_assert!(h.len() == a && g.len() == b);
        let rho_inv = util::invert(rho);
        let mu2 = mu * mu;
        // Pairs (even, odd): [v]_0 and [v]_1 of spec §2.1, without copies.
        let mut w = mu2;
        let (mut nn01, mut nn11) = (C::Scalar::ZERO, C::Scalar::ZERO);
        for i in 0..b / 2 {
            nn01 += n[2 * i] * n[2 * i + 1] * w;
            nn11 += n[2 * i + 1] * n[2 * i + 1] * w;
            w *= mu2;
        }
        let (mut cl, mut cl11) = (C::Scalar::ZERO, C::Scalar::ZERO);
        for i in 0..a / 2 {
            cl += c[2 * i] * l[2 * i + 1] + c[2 * i + 1] * l[2 * i];
            cl11 += c[2 * i + 1] * l[2 * i + 1];
        }
        let vx = C::Scalar::from(2u64) * rho_inv * nn01 + cl;
        let vr = nn11 + cl11;
        // X: every folded generator once; an even position meets the odd entry of its pair and
        // conversely (an unpaired last element meets zero). R: the odd positions.
        let get = |v: &[C::Scalar], j: usize| v.get(j).copied().unwrap_or(C::Scalar::ZERO);
        let (rs_, ris) = (rho * s, rho_inv * s);
        let x_l = |j: usize| if j % 2 == 0 { get(&l, j + 1) } else { l[j - 1] };
        let x_n = |j: usize| if j % 2 == 0 { rs_ * get(&n, j + 1) } else { ris * n[j - 1] };
        let r_l = |j: usize| l[j];
        let r_n = |j: usize| s * n[j];
        let msm = |odd: bool, fl: &(dyn Fn(usize) -> C::Scalar + Sync), fnn: &(dyn Fn(usize) -> C::Scalar + Sync)| {
            let ((hn, ht), (gn, gt)) = (h.terms(odd), g.terms(odd));
            C::msm_index(hn + gn, vartime, |v| {
                if v < hn {
                    let (j, k, p) = ht(v);
                    (fl(j) * k, p)
                } else {
                    let (j, k, p) = gt(v - hn);
                    (fnn(j) * k, p)
                }
            })
        };
        let X = C::compress(&(*st.g * vx + msm(false, &x_l, &x_n)));
        let R = C::compress(&(*st.g * vr + msm(true, &r_l, &r_n)));
        transcript.append_point(b"X", &X);
        transcript.append_point(b"R", &R);
        let gamma: C::Scalar = transcript.challenge(b"gamma");
        xs.push(X);
        rs.push(R);
        if a > 1 {
            c = fold(&c, C::Scalar::ONE, gamma);
            l = fold(&l, C::Scalar::ONE, gamma);
            h.fold(gamma, defer);
        }
        // A norm vector of length 1 stays as it is, and so do rho and mu (spec §2.1).
        if b > 1 {
            n = fold(&n, rho_inv, gamma);
            // N' = rho N_0 + gamma N_1 = s rho (N'_0 + (gamma / rho) N'_1)
            g.fold(gamma * rho_inv, defer);
            s *= rho;
            rho = mu;
            mu = mu2;
        }
    }
    Ok(WnlaProof { X: xs, R: rs, l, n })
}

impl<C: Curve> WnlaProof<C> {
    /// Replay the transcript and compute the scalars of the final check for `|l| = c.len()`,
    /// `|n| = b`. Does not absorb the statement: the counterpart of [`prove_unbound`], for
    /// the circuit protocol.
    pub(crate) fn verification_scalars<T: BpppTranscript + ?Sized>(
        &self,
        c: &[C::Scalar],
        rho: C::Scalar,
        b: usize,
        transcript: &mut T,
    ) -> Result<WnlaScalars<C::Scalar>, ProofError> {
        let a = c.len();
        let (k, af, bf) = rounds(a, b);
        if self.X.len() != k || self.R.len() != k || self.l.len() != af || self.n.len() != bf {
            return Err(ProofError::VerificationError);
        }
        if rho == C::Scalar::ZERO {
            return Err(ProofError::VerificationError);
        }
        absorb_header::<C, T>(transcript, a, b);
        let mut gammas: Vec<C::Scalar> = Vec::with_capacity(k);
        for (X, R) in self.X.iter().zip(&self.R) {
            transcript.append_point(b"X", X);
            transcript.append_point(b"R", R);
            gammas.push(transcript.challenge(b"gamma"));
        }

        // rho advances only in rounds that fold the norm vector (|n| > 1); a frozen round
        // contributes the factor 1.
        let mut c_f = c.to_vec();
        let mut rhos = Vec::with_capacity(k);
        let (mut rho_r, mut b_r) = (rho, b);
        for &gamma in &gammas {
            c_f = fold(&c_f, C::Scalar::ONE, gamma);
            if b_r > 1 {
                rhos.push(rho_r);
                rho_r = rho_r * rho_r;
            } else {
                rhos.push(C::Scalar::ONE);
            }
            b_r -= b_r / 2;
        }
        let v = ip(&c_f, &self.l) + wip(&self.n, &self.n, rho_r * rho_r);

        // Coefficient of index i after k rounds: prod_r (bit r of i ? gamma_r : e_r), with
        // e_r = 1 for H and the round's rho for N; i maps to final index i >> k.
        let tensor = |e: &dyn Fn(usize) -> C::Scalar| {
            let mut t = vec![C::Scalar::ONE];
            for (r, gamma) in gammas.iter().enumerate() {
                let hi: Vec<C::Scalar> = t.iter().map(|x| *x * gamma).collect();
                t.iter_mut().for_each(|x| *x *= e(r));
                t.extend(hi);
            }
            t
        };
        let mask = (1usize << k) - 1;
        let th = tensor(&|_| C::Scalar::ONE);
        let tn = tensor(&|r| rhos[r]);
        let h = (0..a).map(|i| self.l[i >> k] * th[i & mask]).collect();
        let n = (0..b).map(|i| self.n[i >> k] * tn[i & mask]).collect();
        Ok(WnlaScalars { g: v, h, n, gammas })
    }

    /// Prove knowledge of the opening `(l, n)` of `C`. Absorbs `G`, `C`, `rho` and `c` before the
    /// rounds, so the challenges bind the whole statement.
    pub fn prove<T: BpppTranscript + ?Sized>(
        st: &WnlaStatement<C>,
        com: &C::Point,
        transcript: &mut T,
        l: Vec<C::Scalar>,
        n: Vec<C::Scalar>,
    ) -> Result<WnlaProof<C>, ProofError> {
        prove(st, com, transcript, l, n)
    }

    /// Verify against the commitment `C`; absorbs `G`, `C`, `rho` and `c` like
    /// [`WnlaProof::prove`].
    pub fn verify<T: BpppTranscript + ?Sized>(
        &self,
        st: &WnlaStatement<C>,
        com: &C::Point,
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        st.check(st.c.len(), st.n.len())?;
        absorb_statement(transcript, st, &C::compress(com));
        let s = self.verification_scalars(st.c, st.rho, st.n.len(), transcript)?;
        let decompress = |p: &C::Compressed| C::decompress(p).ok_or(ProofError::VerificationError);
        let xs = self.X.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let rs = self.R.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        // g G + <h, H> + <n, N> - C - sum gamma_i X_i + sum (1 - gamma_i^2) R_i = 0
        let points = once((-C::Scalar::ONE, *com))
            .chain(s.gammas.iter().zip(xs).map(|(g, x)| (-*g, x)))
            .chain(s.gammas.iter().zip(rs).map(|(g, r)| (C::Scalar::ONE - *g * g, r)))
            .collect();
        Terms::<C> { g: s.g, h: s.h, n: s.n, points }.check_with(st.g, st.h, st.n)
    }

    /// `X_0 R_0 ... X_{k-1} R_{k-1} l n`, 32 bytes each.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(C::POINT_BYTES * 2 * self.X.len() + 32 * (self.l.len() + self.n.len()));
        for (X, R) in self.X.iter().zip(&self.R) {
            out.extend_from_slice(X.as_bytes());
            out.extend_from_slice(R.as_bytes());
        }
        self.l.iter().chain(&self.n).for_each(|s| out.extend_from_slice(&s.to_bytes32()));
        out
    }

    /// Parse a proof for `|l| = a`, `|n| = b`; rejects wrong lengths and non-canonical scalars.
    pub fn from_bytes(bytes: &[u8], a: usize, b: usize) -> Result<Self, ProofError> {
        let (k, af, bf) = rounds(a, b);
        let pb = C::POINT_BYTES;
        if bytes.len() != pb * 2 * k + 32 * (af + bf) {
            return Err(ProofError::FormatError);
        }
        let (points, scalars) = bytes.split_at(pb * 2 * k);
        let mut points = points.chunks_exact(pb).map(|p| C::Compressed::from_slice(p).ok_or(ProofError::FormatError));
        let mut X = Vec::with_capacity(k);
        let mut R = Vec::with_capacity(k);
        for _ in 0..k {
            X.push(points.next().unwrap()?);
            R.push(points.next().unwrap()?);
        }
        let scalars = scalars
            .chunks_exact(32)
            .map(|b| C::Scalar::from_bytes32(&util::read32(b)).ok_or(ProofError::FormatError))
            .collect::<Result<Vec<_>, _>>()?;
        let (l, n) = scalars.split_at(af);
        Ok(WnlaProof { X, R, l: l.to_vec(), n: n.to_vec() })
    }
}

#[cfg(test)]
mod tests {
    use crate::bppp::testutil::{sc, scs};
    use super::*;
    use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
    use curve25519_dalek::scalar::Scalar;
    use crate::bppp::transcript::Replay;
    use curve25519_dalek::traits::MultiscalarMul;
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use sha3::Sha3_512;

    fn gens(label: &str, n: usize) -> Vec<RistrettoPoint> {
        (0..n)
            .map(|i| RistrettoPoint::hash_from_bytes::<Sha3_512>(format!("{label}{i}").as_bytes()))
            .collect()
    }

    /// The stop rule is secp256k1-zkp's size-optimal layout (PR #352): its closed form, ported.
    /// Deferred folding and variable-time multiplications give the same proof as folding in
    /// every round, for every number of deferred rounds and odd lengths.
    #[test]
    fn deferred_rounds_do_not_change_the_proof() {
        let mut rng = rand::thread_rng();
        for &(a, b) in &[(7usize, 1usize), (7, 2), (7, 37), (13, 64), (8, 100), (1, 9), (21, 3)] {
            let (g, h, nv) = (gens("G", 1)[0], gens("H", a), gens("N", b));
            let c: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
            let st = WnlaStatement::<Ristretto> { g: &g, h: &h, n: &nv, c: &c, rho: Scalar::random(&mut rng) };
            let l: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
            let n: Vec<Scalar> = (0..b).map(|_| Scalar::random(&mut rng)).collect();
            let gammas: Vec<Scalar> = (0..20).map(|_| Scalar::random(&mut rng)).collect();
            let p0 = prove_rounds(&st, &mut Replay::new(gammas.clone()), l.clone(), n.clone(), false, 0).unwrap();
            for d in 0..6 {
                for vt in [false, true] {
                    let p = prove_rounds(&st, &mut Replay::new(gammas.clone()), l.clone(), n.clone(), vt, d).unwrap();
                    assert_eq!(p, p0, "a {} b {} defer {} vartime {}", a, b, d, vt);
                }
            }
        }
    }

    #[test]
    fn rounds_match_secp256k1_zkp_optimal_layout() {
        fn log2_ceil(n: usize) -> usize {
            if n <= 1 { 0 } else { (usize::BITS - (n - 1).leading_zeros()) as usize }
        }
        let rounds_to_fit = |n: usize, limit: usize| log2_ceil(1 + (n - 1) / limit);
        for g in 1..300 {
            for h in 1..300 {
                let (mx, mn) = (g.max(h), g.min(h));
                let both3 = rounds_to_fit(mx, 3).max(rounds_to_fit(mn, 3));
                let max5 = rounds_to_fit(mx, 5).max(log2_ceil(mn));
                assert_eq!(rounds(h, g).0, both3.min(max5), "|l| = {}, |n| = {}", h, g);
            }
        }
    }

    fn reference_vectors<C: Curve>()
    where
        C::Scalar: crate::bppp::testutil::TestScalar,
    {
        use crate::bppp::testutil::{label_gens, sym_point, vectors};
        let file = vectors::<C>(
            include_str!("../../tests/vectors/bppp/wnla.json"),
            include_str!("../../tests/vectors/bppp/secp256k1/wnla.json"),
        );
        for case in file["cases"].as_array().unwrap() {
            let a = case["a"].as_u64().unwrap() as usize;
            let b = case["b"].as_u64().unwrap() as usize;
            let (G, H, N) = (label_gens::<C>("G", 1)[0], label_gens::<C>("H", a), label_gens::<C>("N", b));
            let c: Vec<C::Scalar> = scs(&case["c"]);
            let st = WnlaStatement::<C> { g: &G, h: &H, n: &N, c: &c, rho: sc(&case["rho"]) };
            let gammas: Vec<C::Scalar> = scs(&case["gammas"]);
            let (l, n): (Vec<C::Scalar>, Vec<C::Scalar>) = (scs(&case["l"]), scs(&case["n"]));
            let proof = prove_unbound(&st, &mut Replay::new(gammas.clone()), l.clone(), n.clone(), false).unwrap();
            let point = |p: &serde_json::Value| sym_point::<C>(p, &G, &H, &N);
            let rounds = case["rounds"].as_array().unwrap();
            assert_eq!(proof.X.len(), rounds.len(), "case {a}x{b}");
            for (r, round) in rounds.iter().enumerate() {
                assert_eq!(proof.X[r], point(&round["X"]), "X_{r}, case {a}x{b}");
                assert_eq!(proof.R[r], point(&round["R"]), "R_{r}, case {a}x{b}");
            }
            assert_eq!(proof.l, scs::<C::Scalar>(&case["l_final"]));
            assert_eq!(proof.n, scs::<C::Scalar>(&case["n_final"]));
            proof.verify(&st, &st.commit(&l, &n), &mut Replay::new(gammas)).unwrap();
        }
    }

    #[test]
    fn matches_reference_vectors() {
        reference_vectors::<Ristretto>();
    }

    #[cfg(feature = "secp256k1")]
    #[test]
    fn matches_reference_vectors_secp256k1() {
        reference_vectors::<crate::curve::Secp256k1>();
    }

    /// A standalone verifier must bind the commitment: otherwise a prover fixes `X_r`, `R_r`
    /// and the final vectors first and solves the verification equation for `C`.
    #[test]
    fn standalone_verify_rejects_forged_commitment() {
        let (G, H, N) = (gens("G", 1)[0], gens("H", 8), gens("N", 8));
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let c: Vec<Scalar> = (0..8).map(|_| Scalar::random(&mut rng)).collect();
        let st = WnlaStatement::<Ristretto> { g: &G, h: &H, n: &N, c: &c, rho: Scalar::random(&mut rng) };
        let (k, af, bf) = rounds(8, 8);
        let xs: Vec<Scalar> = (0..k).map(|_| Scalar::random(&mut rng)).collect();
        let ys: Vec<Scalar> = (0..k).map(|_| Scalar::random(&mut rng)).collect();
        let forged = WnlaProof {
            X: xs.iter().map(|x| (G * x).compress()).collect(),
            R: ys.iter().map(|y| (G * y).compress()).collect(),
            l: (0..af).map(|_| Scalar::random(&mut rng)).collect(),
            n: (0..bf).map(|_| Scalar::random(&mut rng)).collect(),
        };
        let s = forged.verification_scalars(&c, st.rho, 8, &mut Transcript::new(b"app")).unwrap();
        let folded: Scalar = s
            .gammas
            .iter()
            .zip(xs.iter().zip(&ys))
            .map(|(g, (x, y))| g * x + (g * g - Scalar::ONE) * y)
            .sum();
        let C = G * (s.g - folded)
            + RistrettoPoint::multiscalar_mul(&s.h, &H)
            + RistrettoPoint::multiscalar_mul(&s.n, &N);
        assert!(forged.verify(&st, &C, &mut Transcript::new(b"app")).is_err());
    }

    /// The prover absorbs the statement, the lengths and every `(X_r, R_r)` before the
    /// challenge of its round, and the verifier absorbs exactly the same bytes.
    #[test]
    fn transcript_binds_messages() {
        let (G, H, N) = (gens("G", 1)[0], gens("H", 9), gens("N", 13));
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let c: Vec<Scalar> = (0..9).map(|_| Scalar::random(&mut rng)).collect();
        let st = WnlaStatement::<Ristretto> { g: &G, h: &H, n: &N, c: &c, rho: Scalar::random(&mut rng) };
        let l: Vec<Scalar> = (0..9).map(|_| Scalar::random(&mut rng)).collect();
        let n: Vec<Scalar> = (0..13).map(|_| Scalar::random(&mut rng)).collect();
        let C = st.commit(&l, &n);
        let challenges: Vec<Scalar> = (1..=3u64).map(Scalar::from).collect();
        let mut t = Replay::new(challenges.clone());
        let proof = prove(&st, &C, &mut t, l, n).unwrap();

        let mut expected: Vec<(&[u8], Vec<u8>)> = vec![
            (b"bppp-wnla-statement v1", vec![]),
            (b"G", G.compress().as_bytes().to_vec()),
            (b"C", C.compress().as_bytes().to_vec()),
            (b"rho", st.rho.as_bytes().to_vec()),
        ];
        expected.extend(c.iter().map(|x| (&b"c"[..], x.as_bytes().to_vec())));
        expected.extend([
            (&b"bppp-wnla v1"[..], vec![]),
            (b"l", 9u64.to_le_bytes().to_vec()),
            (b"n", 13u64.to_le_bytes().to_vec()),
        ]);
        assert_eq!(proof.X.len(), 3);
        for r in 0..3 {
            expected.extend([
                (&b"X"[..], proof.X[r].as_bytes().to_vec()),
                (b"R", proof.R[r].as_bytes().to_vec()),
                (b"gamma", vec![]),
            ]);
        }
        assert_eq!(t.log, expected, "prover");

        let mut tv = Replay::new(challenges);
        proof.verify(&st, &C, &mut tv).unwrap();
        assert_eq!(tv.log, expected, "verifier");
    }

    #[test]
    fn prove_verify_tamper() {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        for (a, b) in [(0, 0), (1, 1), (5, 0), (0, 6), (8, 8), (9, 13), (1, 64), (64, 1), (30, 17)] {
            let (G, H, N) = (gens("G", 1)[0], gens("H", a), gens("N", b));
            let c: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
            let st = WnlaStatement::<Ristretto> { g: &G, h: &H, n: &N, c: &c, rho: Scalar::random(&mut rng) };
            let l: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
            let n: Vec<Scalar> = (0..b).map(|_| Scalar::random(&mut rng)).collect();
            let C = st.commit(&l, &n);
            let proof = prove(&st, &C, &mut Transcript::new(b"t"), l, n).unwrap();
            let ok = |p: &WnlaProof, C: &RistrettoPoint| p.verify(&st, C, &mut Transcript::new(b"t")).is_ok();
            assert!(ok(&proof, &C), "{}x{}", a, b);
            assert_eq!(WnlaProof::<Ristretto>::from_bytes(&proof.to_bytes(), a, b).unwrap(), proof);
            assert!(!ok(&proof, &(C + G)), "{}x{}: wrong commitment", a, b);
            if !proof.l.is_empty() {
                let mut p = proof.clone();
                p.l[0] += Scalar::ONE;
                assert!(!ok(&p, &C), "{}x{}: l", a, b);
            }
            if !proof.n.is_empty() {
                let mut p = proof.clone();
                p.n[0] += Scalar::ONE;
                assert!(!ok(&p, &C), "{}x{}: n", a, b);
            }
            if !proof.X.is_empty() {
                let mut p = proof.clone();
                p.X[0] = proof.R[0];
                assert!(!ok(&p, &C), "{}x{}: X", a, b);
            }
        }
    }

    #[test]
    fn malformed_proofs_are_errors() {
        let (G, H, N) = (gens("G", 1)[0], gens("H", 8), gens("N", 8));
        let c = vec![Scalar::ONE; 8];
        let st = WnlaStatement::<Ristretto> { g: &G, h: &H, n: &N, c: &c, rho: Scalar::from(3u64) };
        let (l, n) = (vec![Scalar::from(5u64); 8], vec![Scalar::from(7u64); 8]);
        let C = st.commit(&l, &n);
        let proof = prove(&st, &C, &mut Transcript::new(b"t"), l, n).unwrap();
        let bytes = proof.to_bytes();
        assert!(WnlaProof::<Ristretto>::from_bytes(&bytes[1..], 8, 8).is_err());
        assert!(WnlaProof::<Ristretto>::from_bytes(&bytes, 8, 9).is_err());
        let mut non_canonical = bytes.clone();
        let last = non_canonical.len() - 32;
        non_canonical[last..].copy_from_slice(&[0xff; 32]);
        assert!(WnlaProof::<Ristretto>::from_bytes(&non_canonical, 8, 8).is_err());
        let mut extra = proof.clone();
        extra.X.push(proof.X[0]);
        extra.R.push(proof.R[0]);
        assert!(extra.verify(&st, &C, &mut Transcript::new(b"t")).is_err());
        let mut bad_point = proof.clone();
        bad_point.X[0] = CompressedRistretto([0xff; 32]);
        assert!(bad_point.verify(&st, &C, &mut Transcript::new(b"t")).is_err());
        let zero_rho = WnlaStatement { rho: Scalar::ZERO, ..st };
        assert!(prove(&zero_rho, &C, &mut Transcript::new(b"t"), vec![Scalar::ONE; 8], vec![Scalar::ONE; 8]).is_err());
    }
}

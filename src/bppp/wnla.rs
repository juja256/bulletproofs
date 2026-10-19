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

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use super::transcript::BpppTranscript;
use crate::errors::ProofError;
use crate::util;

/// Public input of the argument. `h_vec` and `c` have the length of `l`, `n_vec` that of `n`.
pub struct WnlaStatement<'a> {
    /// Value generator `G`.
    pub g: &'a RistrettoPoint,
    /// Generators of the linear part `l`.
    pub h_vec: &'a [RistrettoPoint],
    /// Generators of the norm part `n`.
    pub n_vec: &'a [RistrettoPoint],
    /// Linear constraint vector.
    pub c: &'a [Scalar],
    /// Square root of the norm weight, `mu = rho^2`; non-zero.
    pub rho: Scalar,
}

/// A WNLA proof: one `(X, R)` pair per round and the final vectors.
#[derive(Clone, Debug, PartialEq)]
pub struct WnlaProof {
    /// `X_r`, the `gamma` coefficients.
    pub X: Vec<CompressedRistretto>,
    /// `R_r`, the `gamma^2 - 1` coefficients.
    pub R: Vec<CompressedRistretto>,
    /// Final `l`.
    pub l: Vec<Scalar>,
    /// Final `n`.
    pub n: Vec<Scalar>,
}

/// Scalars of the verification equation (spec §2.4):
/// `g*G + <h, H> + <n, N> - C - sum_r (gamma_r X_r + (gamma_r^2 - 1) R_r) = 0`.
/// The circuit verifier merges them into its own multiscalar multiplication.
pub struct WnlaScalars {
    /// Coefficient of `G` (the value `v` of the final vectors).
    pub g: Scalar,
    /// Coefficients of `H`.
    pub h: Vec<Scalar>,
    /// Coefficients of `N`.
    pub n: Vec<Scalar>,
    /// The round challenges.
    pub gammas: Vec<Scalar>,
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
        a = (a + 1) / 2;
        b = (b + 1) / 2;
        k += 1;
    }
    (k, a, b)
}

fn ip(a: &[Scalar], b: &[Scalar]) -> Scalar {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

/// `<a, b>_mu = sum_i a_i b_i mu^(i+1)`.
fn wip(a: &[Scalar], b: &[Scalar], mu: Scalar) -> Scalar {
    let mut w = mu;
    let mut acc = Scalar::ZERO;
    for (x, y) in a.iter().zip(b) {
        acc += x * y * w;
        w *= mu;
    }
    acc
}

fn split<T: Copy>(v: &[T]) -> (Vec<T>, Vec<T>) {
    (v.iter().step_by(2).copied().collect(), v.iter().skip(1).step_by(2).copied().collect())
}

/// `e*[v]_0 + g*[v]_1`, zero-padded on the right: length `ceil(|v|/2)`.
fn fold(v: &[Scalar], e: Scalar, g: Scalar) -> Vec<Scalar> {
    util::map_index((v.len() + 1) / 2, |i| {
        e * v[2 * i] + v.get(2 * i + 1).map_or(Scalar::ZERO, |x| g * x)
    })
}

/// [`fold`] for generators (public scalars, variable time).
fn fold_points(p: &[RistrettoPoint], e: Scalar, g: Scalar) -> Vec<RistrettoPoint> {
    util::map_index((p.len() + 1) / 2, |i| match p.get(2 * i + 1) {
        Some(hi) => RistrettoPoint::vartime_multiscalar_mul([e, g], [p[2 * i], *hi]),
        None => p[2 * i] * e,
    })
}

/// Constant-time `sum_i s_i P_i` over the common prefix (implicit zero padding).
fn ct_msm(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
    let m = s.len().min(p.len());
    util::msm_slices(&s[..m], &p[..m], util::MSM_CHUNK_CT, false)
}

impl WnlaStatement<'_> {
    fn check(&self, a: usize, b: usize) -> Result<(), ProofError> {
        if self.h_vec.len() != a || self.c.len() != a || self.n_vec.len() != b {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if self.rho == Scalar::ZERO {
            return Err(ProofError::FormatError);
        }
        Ok(())
    }

    /// `v*G + <l, H> + <n, N>` with `v = <c, l> + |n|^2_mu` (constant time).
    pub fn commit(&self, l: &[Scalar], n: &[Scalar]) -> RistrettoPoint {
        let v = ip(self.c, l) + wip(n, n, self.rho * self.rho);
        self.g * v + ct_msm(l, self.h_vec) + ct_msm(n, self.n_vec)
    }
}

fn absorb_header<T: BpppTranscript>(transcript: &mut T, a: usize, b: usize) {
    transcript.domain_sep(b"bppp-wnla v1");
    transcript.append_u64(b"l", a as u64);
    transcript.append_u64(b"n", b as u64);
}

/// Absorb the public input of a standalone argument (spec §2.3).
fn absorb_statement<T: BpppTranscript>(transcript: &mut T, st: &WnlaStatement, C: &CompressedRistretto) {
    transcript.domain_sep(b"bppp-wnla-statement v1");
    transcript.append_point(b"G", &st.g.compress());
    transcript.append_point(b"C", C);
    transcript.append_scalar(b"rho", &st.rho);
    st.c.iter().for_each(|c| transcript.append_scalar(b"c", c));
}

/// Prove knowledge of the opening `(l, n)` of `C`. Absorbs `G`, `C`, `rho` and `c` before the
/// rounds, so the challenges bind the whole statement.
pub fn prove<T: BpppTranscript>(
    st: &WnlaStatement,
    C: &RistrettoPoint,
    transcript: &mut T,
    l: Vec<Scalar>,
    n: Vec<Scalar>,
) -> Result<WnlaProof, ProofError> {
    st.check(l.len(), n.len())?;
    absorb_statement(transcript, st, &C.compress());
    prove_unbound(st, transcript, l, n)
}

/// [`prove`] without absorbing the statement, for the circuit protocol: there `C`, `c` and
/// `rho` are functions of commitments and challenges already in the transcript, and
/// computing `C` explicitly would cost a full multiscalar multiplication.
pub(crate) fn prove_unbound<T: BpppTranscript>(
    st: &WnlaStatement,
    transcript: &mut T,
    mut l: Vec<Scalar>,
    mut n: Vec<Scalar>,
) -> Result<WnlaProof, ProofError> {
    st.check(l.len(), n.len())?;
    absorb_header(transcript, l.len(), n.len());
    let (mut c, mut h, mut g) = (st.c.to_vec(), st.h_vec.to_vec(), st.n_vec.to_vec());
    let (mut rho, mut mu) = (st.rho, st.rho * st.rho);
    let (mut xs, mut rs) = (Vec::new(), Vec::new());
    while more(l.len(), n.len()) {
        let rho_inv = rho.invert();
        let mu2 = mu * mu;
        let (l0, l1) = split(&l);
        let (n0, n1) = split(&n);
        let (c0, c1) = split(&c);
        let (h0, h1) = split(&h);
        let (g0, g1) = split(&g);
        let vx = Scalar::from(2u64) * rho_inv * wip(&n0, &n1, mu2) + ip(&c0, &l1) + ip(&c1, &l0);
        let vr = wip(&n1, &n1, mu2) + ip(&c1, &l1);
        let rho_n1: Vec<Scalar> = n1.iter().map(|x| rho * x).collect();
        let rho_inv_n0: Vec<Scalar> = n0.iter().map(|x| rho_inv * x).collect();
        let X = (st.g * vx + ct_msm(&l1, &h0) + ct_msm(&l0, &h1) + ct_msm(&rho_n1, &g0)
            + ct_msm(&rho_inv_n0, &g1))
        .compress();
        let R = (st.g * vr + ct_msm(&l1, &h1) + ct_msm(&n1, &g1)).compress();
        transcript.append_point(b"X", &X);
        transcript.append_point(b"R", &R);
        let gamma = transcript.challenge(b"gamma");
        xs.push(X);
        rs.push(R);
        if l.len() > 1 {
            c = fold(&c, Scalar::ONE, gamma);
            l = fold(&l, Scalar::ONE, gamma);
            h = fold_points(&h, Scalar::ONE, gamma);
        }
        // A norm vector of length 1 stays as it is, and so do rho and mu (spec §2.1).
        if n.len() > 1 {
            n = fold(&n, rho_inv, gamma);
            g = fold_points(&g, rho, gamma);
            rho = mu;
            mu = mu2;
        }
    }
    Ok(WnlaProof { X: xs, R: rs, l, n })
}

impl WnlaProof {
    /// Replay the transcript and compute the scalars of the final check for `|l| = c.len()`,
    /// `|n| = b`. Does not absorb the statement: the counterpart of [`prove_unbound`], for
    /// the circuit protocol.
    pub(crate) fn verification_scalars<T: BpppTranscript>(
        &self,
        c: &[Scalar],
        rho: Scalar,
        b: usize,
        transcript: &mut T,
    ) -> Result<WnlaScalars, ProofError> {
        let a = c.len();
        let (k, af, bf) = rounds(a, b);
        if self.X.len() != k || self.R.len() != k || self.l.len() != af || self.n.len() != bf {
            return Err(ProofError::VerificationError);
        }
        if rho == Scalar::ZERO {
            return Err(ProofError::VerificationError);
        }
        absorb_header(transcript, a, b);
        let mut gammas = Vec::with_capacity(k);
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
            c_f = fold(&c_f, Scalar::ONE, gamma);
            if b_r > 1 {
                rhos.push(rho_r);
                rho_r = rho_r * rho_r;
            } else {
                rhos.push(Scalar::ONE);
            }
            b_r = (b_r + 1) / 2;
        }
        let v = ip(&c_f, &self.l) + wip(&self.n, &self.n, rho_r * rho_r);

        // Coefficient of index i after k rounds: prod_r (bit r of i ? gamma_r : e_r), with
        // e_r = 1 for H and the round's rho for N; i maps to final index i >> k.
        let tensor = |e: &dyn Fn(usize) -> Scalar| {
            let mut t = vec![Scalar::ONE];
            for (r, gamma) in gammas.iter().enumerate() {
                let hi: Vec<Scalar> = t.iter().map(|x| x * gamma).collect();
                t.iter_mut().for_each(|x| *x *= e(r));
                t.extend(hi);
            }
            t
        };
        let mask = (1usize << k) - 1;
        let th = tensor(&|_| Scalar::ONE);
        let tn = tensor(&|r| rhos[r]);
        let h = (0..a).map(|i| self.l[i >> k] * th[i & mask]).collect();
        let n = (0..b).map(|i| self.n[i >> k] * tn[i & mask]).collect();
        Ok(WnlaScalars { g: v, h, n, gammas })
    }

    /// Verify against the commitment `C`; absorbs `G`, `C`, `rho` and `c` like [`prove`].
    pub fn verify<T: BpppTranscript>(
        &self,
        st: &WnlaStatement,
        C: &RistrettoPoint,
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        st.check(st.c.len(), st.n_vec.len())?;
        absorb_statement(transcript, st, &C.compress());
        let s = self.verification_scalars(st.c, st.rho, st.n_vec.len(), transcript)?;
        let decompress = |p: &CompressedRistretto| p.decompress().ok_or(ProofError::VerificationError);
        let xs = self.X.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let rs = self.R.iter().map(decompress).collect::<Result<Vec<_>, _>>()?;
        let small = RistrettoPoint::vartime_multiscalar_mul(
            once(s.g)
                .chain(once(-Scalar::ONE))
                .chain(s.gammas.iter().map(|g| -g))
                .chain(s.gammas.iter().map(|g| Scalar::ONE - g * g)),
            once(st.g).chain(once(C)).chain(xs.iter()).chain(rs.iter()),
        );
        let check = small
            + util::vartime_msm_slices(&s.h, st.h_vec, util::MSM_CHUNK_VT)
            + util::vartime_msm_slices(&s.n, st.n_vec, util::MSM_CHUNK_VT);
        if check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// `X_0 R_0 ... X_{k-1} R_{k-1} l n`, 32 bytes each.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(32 * (2 * self.X.len() + self.l.len() + self.n.len()));
        for (X, R) in self.X.iter().zip(&self.R) {
            out.extend_from_slice(X.as_bytes());
            out.extend_from_slice(R.as_bytes());
        }
        self.l.iter().chain(&self.n).for_each(|s| out.extend_from_slice(s.as_bytes()));
        out
    }

    /// Parse a proof for `|l| = a`, `|n| = b`; rejects wrong lengths and non-canonical scalars.
    pub fn from_bytes(bytes: &[u8], a: usize, b: usize) -> Result<Self, ProofError> {
        let (k, af, bf) = rounds(a, b);
        if bytes.len() != 32 * (2 * k + af + bf) {
            return Err(ProofError::FormatError);
        }
        let mut chunks = bytes.chunks_exact(32).map(util::read32);
        let mut X = Vec::with_capacity(k);
        let mut R = Vec::with_capacity(k);
        for _ in 0..k {
            X.push(CompressedRistretto(chunks.next().unwrap()));
            R.push(CompressedRistretto(chunks.next().unwrap()));
        }
        let scalars = chunks
            .map(|b| Option::from(Scalar::from_canonical_bytes(b)).ok_or(ProofError::FormatError))
            .collect::<Result<Vec<_>, _>>()?;
        let (l, n) = scalars.split_at(af);
        Ok(WnlaProof { X, R, l: l.to_vec(), n: n.to_vec() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::TryInto;
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

    fn sc(v: &serde_json::Value) -> Scalar {
        let b: [u8; 32] = hex::decode(v.as_str().unwrap()).unwrap().try_into().unwrap();
        Scalar::from_canonical_bytes(b).unwrap()
    }

    fn scs(v: &serde_json::Value) -> Vec<Scalar> {
        v.as_array().unwrap().iter().map(sc).collect()
    }

    /// The stop rule is secp256k1-zkp's size-optimal layout (PR #352): its closed form, ported.
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

    #[test]
    fn matches_reference_vectors() {
        let file: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/bppp/wnla.json")).unwrap();
        for case in file["cases"].as_array().unwrap() {
            let a = case["a"].as_u64().unwrap() as usize;
            let b = case["b"].as_u64().unwrap() as usize;
            let (G, H, N) = (gens("G", 1)[0], gens("H", a), gens("N", b));
            let c = scs(&case["c"]);
            let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &c, rho: sc(&case["rho"]) };
            let gammas = scs(&case["gammas"]);
            let (l, n) = (scs(&case["l"]), scs(&case["n"]));
            let proof = prove_unbound(&st, &mut Replay::new(gammas.clone()), l.clone(), n.clone()).unwrap();
            let point = |p: &serde_json::Value| {
                (G * sc(&p["g"])
                    + RistrettoPoint::multiscalar_mul(scs(&p["h"]), &H)
                    + RistrettoPoint::multiscalar_mul(scs(&p["n"]), &N))
                .compress()
            };
            let rounds = case["rounds"].as_array().unwrap();
            assert_eq!(proof.X.len(), rounds.len(), "case {a}x{b}");
            for (r, round) in rounds.iter().enumerate() {
                assert_eq!(proof.X[r], point(&round["X"]), "X_{r}, case {a}x{b}");
                assert_eq!(proof.R[r], point(&round["R"]), "R_{r}, case {a}x{b}");
            }
            assert_eq!(proof.l, scs(&case["l_final"]));
            assert_eq!(proof.n, scs(&case["n_final"]));
            proof.verify(&st, &st.commit(&l, &n), &mut Replay::new(gammas)).unwrap();
        }
    }

    /// A standalone verifier must bind the commitment: otherwise a prover fixes `X_r`, `R_r`
    /// and the final vectors first and solves the verification equation for `C`.
    #[test]
    fn standalone_verify_rejects_forged_commitment() {
        let (G, H, N) = (gens("G", 1)[0], gens("H", 8), gens("N", 8));
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let c: Vec<Scalar> = (0..8).map(|_| Scalar::random(&mut rng)).collect();
        let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &c, rho: Scalar::random(&mut rng) };
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
        let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &c, rho: Scalar::random(&mut rng) };
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
            let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &c, rho: Scalar::random(&mut rng) };
            let l: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
            let n: Vec<Scalar> = (0..b).map(|_| Scalar::random(&mut rng)).collect();
            let C = st.commit(&l, &n);
            let proof = prove(&st, &C, &mut Transcript::new(b"t"), l, n).unwrap();
            let ok = |p: &WnlaProof, C: &RistrettoPoint| p.verify(&st, C, &mut Transcript::new(b"t")).is_ok();
            assert!(ok(&proof, &C), "{}x{}", a, b);
            assert_eq!(WnlaProof::from_bytes(&proof.to_bytes(), a, b).unwrap(), proof);
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
        let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &c, rho: Scalar::from(3u64) };
        let (l, n) = (vec![Scalar::from(5u64); 8], vec![Scalar::from(7u64); 8]);
        let C = st.commit(&l, &n);
        let proof = prove(&st, &C, &mut Transcript::new(b"t"), l, n).unwrap();
        let bytes = proof.to_bytes();
        assert!(WnlaProof::from_bytes(&bytes[1..], 8, 8).is_err());
        assert!(WnlaProof::from_bytes(&bytes, 8, 9).is_err());
        let mut non_canonical = bytes.clone();
        let last = non_canonical.len() - 32;
        non_canonical[last..].copy_from_slice(&[0xff; 32]);
        assert!(WnlaProof::from_bytes(&non_canonical, 8, 8).is_err());
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

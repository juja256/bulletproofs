#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;
use crate::util;

#[derive(Clone, Debug)]
pub struct InnerProductProof {
    pub(crate) L_vec: Vec<CompressedRistretto>,
    pub(crate) R_vec: Vec<CompressedRistretto>,
    pub(crate) a: Scalar,
    pub(crate) b: Scalar,
}

/// `lo[i] = x * lo[i] + y * hi[i]`.
/// Number of initial rounds of [`InnerProductProof::create_with_factor_fns`] that compute
/// L and R from the input generators instead of folding them.
const DEFERRED_ROUNDS: usize = 4;

fn fold_scalars(lo: &mut [Scalar], hi: &[Scalar], x: Scalar, y: Scalar) {
    for (l, h) in lo.iter_mut().zip(hi) {
        *l = *l * x + y * h;
    }
}

/// `lo[i] = x * lo[i] + y * hi[i]` (variable time; in parallel with `parallel`).
fn fold_points(lo: &mut [RistrettoPoint], hi: &[RistrettoPoint], x: Scalar, y: Scalar) {
    let f = |(l, h): (&mut RistrettoPoint, &RistrettoPoint)| {
        *l = RistrettoPoint::vartime_multiscalar_mul(&[x, y], &[*l, *h]);
    };
    #[cfg(feature = "parallel")]
    {
        use rayon::prelude::*;
        lo.par_iter_mut().zip(hi.par_iter()).for_each(f);
    }
    #[cfg(not(feature = "parallel"))]
    lo.iter_mut().zip(hi.iter()).for_each(f);
}

impl InnerProductProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &RistrettoPoint,
        G_factors: &[Scalar],
        H_factors: &[Scalar],
        G_vec: Vec<RistrettoPoint>,
        H_vec: Vec<RistrettoPoint>,
        a_vec: Vec<Scalar>,
        b_vec: Vec<Scalar>,
    ) -> InnerProductProof {
        Self::create_from_slices(transcript, Q, G_factors, H_factors, &G_vec, &H_vec, a_vec, b_vec)
    }

    /// As [`InnerProductProof::create`], but reads the generators from slices.
    pub fn create_from_slices(
        transcript: &mut Transcript,
        Q: &RistrettoPoint,
        G_factors: &[Scalar],
        H_factors: &[Scalar],
        G_in: &[RistrettoPoint],
        H_in: &[RistrettoPoint],
        a_vec: Vec<Scalar>,
        b_vec: Vec<Scalar>,
    ) -> InnerProductProof {
        assert_eq!(G_factors.len(), G_in.len());
        assert_eq!(H_factors.len(), G_in.len());
        Self::create_with_factor_fns(
            transcript,
            Q,
            |i| G_factors[i],
            |i| H_factors[i],
            G_in,
            H_in,
            a_vec,
            b_vec,
        )
    }

    /// The inner-product argument for the bases \\(G_i \cdot g(i)\\), \\(H_i \cdot h(i)\\),
    /// with the factors given as functions of the index.
    ///
    /// Folding a generator costs about as much as six terms of a large multiscalar
    /// multiplication, so the first [`DEFERRED_ROUNDS`] rounds do not fold. After \\(r\\)
    /// rounds the folded generators are \\(G'_i = \sum_t c_t g(i + tB) G_{i+tB}\\) with block
    /// size \\(B = n/2^r\\) and \\(c_t\\) a product of \\(u_j^{\pm 1}\\) selected by the bits of
    /// \\(t\\), so \\(L\\) and \\(R\\) are multiscalar multiplications over the input generators.
    /// The folded generators are then materialised once, each as a \\(2^r\\)-term combination,
    /// and the remaining rounds fold as usual. The proof is the same as with folding in every
    /// round; the input generators are not copied and only \\(2n/2^r\\) points are allocated.
    pub(crate) fn create_with_factor_fns<GF, HF>(
        transcript: &mut Transcript,
        Q: &RistrettoPoint,
        gf: GF,
        hf: HF,
        G_in: &[RistrettoPoint],
        H_in: &[RistrettoPoint],
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>,
    ) -> InnerProductProof
    where
        GF: Fn(usize) -> Scalar + Sync,
        HF: Fn(usize) -> Scalar + Sync,
    {
        let total = G_in.len();
        let mut n = total;

        assert_eq!(H_in.len(), n);
        assert_eq!(a_vec.len(), n);
        assert_eq!(b_vec.len(), n);
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        // Deferred rounds. `cg[t]`, `ch[t]`: coefficients of block `t` of the input
        // generators in the current folded G and H.
        let k = DEFERRED_ROUNDS.min(lg_n);
        let mut cg = vec![Scalar::ONE];
        let mut ch = vec![Scalar::ONE];
        for _ in 0..k {
            let block = n;
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            // Input index v lies in block t = v / block at folded position w = v % block:
            // L = <a_L, G'_hi> + <b_R, H'_lo> + c_L Q,  R = <a_R, G'_lo> + <b_L, H'_hi> + c_R Q.
            let (aL, aR, bL, bR) = (&*a_L, &*a_R, &*b_L, &*b_R);
            let (cg_, ch_, gf_, hf_) = (&cg, &ch, &gf, &hf);
            let L = util::vartime_msm_index(total, util::MSM_CHUNK_VT, |v| {
                let (t, w) = (v / block, v % block);
                if w < n {
                    (bR[w] * ch_[t] * hf_(v), &H_in[v])
                } else {
                    (aL[w - n] * cg_[t] * gf_(v), &G_in[v])
                }
            }) + c_L * Q;
            let R = util::vartime_msm_index(total, util::MSM_CHUNK_VT, |v| {
                let (t, w) = (v / block, v % block);
                if w < n {
                    (aR[w] * cg_[t] * gf_(v), &G_in[v])
                } else {
                    (bL[w - n] * ch_[t] * hf_(v), &H_in[v])
                }
            }) + c_R * Q;
            let (L, R) = (L.compress(), R.compress());

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u: Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            fold_scalars(a_L, a_R, u, u_inv);
            fold_scalars(b_L, b_R, u_inv, u);
            // G' = u^-1 G'_lo + u G'_hi,  H' = u H'_lo + u^-1 H'_hi
            cg = cg.iter().flat_map(|c| [c * u_inv, c * u]).collect();
            ch = ch.iter().flat_map(|c| [c * u, c * u_inv]).collect();

            a = a_L;
            b = b_L;
        }

        if n == 1 {
            return InnerProductProof {
                L_vec,
                R_vec,
                a: a[0],
                b: b[0],
            };
        }

        // Materialise the folded generators: G'_i = sum_t cg[t] g(i + t n) G_{i + t n}.
        let rows = cg.len();
        let materialise = |inputs: &[RistrettoPoint], c: &[Scalar], f: &(dyn Fn(usize) -> Scalar + Sync)| {
            util::map_index(n, |i| {
                RistrettoPoint::vartime_multiscalar_mul(
                    (0..rows).map(|t| c[t] * f(i + t * n)),
                    (0..rows).map(|t| &inputs[i + t * n]),
                )
            })
        };
        let mut G_vec = materialise(G_in, &cg, &gf);
        let mut H_vec = materialise(H_in, &ch, &hf);
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L = (util::vartime_msm_slices(a_L, G_R, util::MSM_CHUNK_VT)
                + util::vartime_msm_slices(b_R, H_L, util::MSM_CHUNK_VT)
                + c_L * Q)
                .compress();
            let R = (util::vartime_msm_slices(a_R, G_L, util::MSM_CHUNK_VT)
                + util::vartime_msm_slices(b_L, H_R, util::MSM_CHUNK_VT)
                + c_R * Q)
                .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u: Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            fold_scalars(a_L, a_R, u, u_inv);
            fold_scalars(b_L, b_R, u_inv, u);
            fold_points(G_L, G_R, u_inv, u);
            fold_points(H_L, H_R, u, u_inv);

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductProof {
            L_vec,
            R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(transcript.challenge_scalar(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        let allinv = Scalar::batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            // XXX missing square fn upstream
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.

        // s[i] = s[i - 2^lg_i] * u_{lg_i + 1}^2 for 2^lg_i <= i < 2^(lg_i + 1): the block
        // [2^lg_i, 2^(lg_i+1)) is the block [0, 2^lg_i) times one square, so each block is
        // computed at once (in parallel with `parallel`).
        let mut s = vec![Scalar::ZERO; n];
        s[0] = allinv;
        for lg_i in 0..lg_n {
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            let (lo, hi) = s.split_at_mut(k);
            let hi = &mut hi[..k];
            #[cfg(feature = "parallel")]
            {
                use rayon::prelude::*;
                hi.par_iter_mut().zip(lo.par_iter()).for_each(|(h, l)| *h = l * u_lg_i_sq);
            }
            #[cfg(not(feature = "parallel"))]
            for (h, l) in hi.iter_mut().zip(lo.iter()) {
                *h = l * u_lg_i_sq;
            }
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<Scalar>,
        IH: IntoIterator,
        IH::Item: Borrow<Scalar>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -ui);

        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let expect_P = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq),
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter()),
        );

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.extend_from_slice(l.as_bytes());
            buf.extend_from_slice(r.as_bytes());
        }
        buf.extend_from_slice(self.a.as_bytes());
        buf.extend_from_slice(self.b.as_bytes());
        buf
    }

    /// Converts the proof into a byte iterator over serialized view of the proof.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    #[inline]
    pub(crate) fn to_bytes_iter(&self) -> impl Iterator<Item = u8> + '_ {
        self.L_vec
            .iter()
            .zip(self.R_vec.iter())
            .flat_map(|(l, r)| l.as_bytes().iter().chain(r.as_bytes()))
            .chain(self.a.as_bytes())
            .chain(self.b.as_bytes())
            .copied()
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+2\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n\\) points are not valid compressed Ristretto points,
    /// * any of 2 scalars are not canonical scalars modulo Ristretto group order.
    pub fn from_bytes(slice: &[u8]) -> Result<InnerProductProof, ProofError> {
        let b = slice.len();
        if b % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / 32;
        if num_elements < 2 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 2) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 2) / 2;
        if lg_n >= 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        let mut L_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = 2 * i * 32;
            L_vec.push(CompressedRistretto(read32(&slice[pos..])));
            R_vec.push(CompressedRistretto(read32(&slice[pos + 32..])));
        }

        let pos = 2 * lg_n * 32;
        let a = Option::from(Scalar::from_canonical_bytes(read32(&slice[pos..])))
            .ok_or(ProofError::FormatError)?;
        let b = Option::from(Scalar::from_canonical_bytes(read32(&slice[pos + 32..])))
            .ok_or(ProofError::FormatError)?;

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::ZERO;
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::util;
    use sha3::Sha3_512;

    fn test_helper_create(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::BulletproofGens;
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n).cloned().collect();
        let H: Vec<RistrettoPoint> = bp_gens.share(0).H(n).cloned().collect();

        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = Scalar::random(&mut rng);
        let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().cloned();

        let P = RistrettoPoint::vartime_multiscalar_mul(
            a_prime.chain(b_prime).chain(iter::once(c)),
            G.iter().chain(H.iter()).chain(iter::once(&Q)),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = InnerProductProof::create(
            &mut verifier,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Scalar::ONE).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());

        let proof = InnerProductProof::from_bytes(proof.to_bytes().as_slice()).unwrap();
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Scalar::ONE).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());
    }

    #[test]
    fn make_ipp_1() {
        test_helper_create(1);
    }

    #[test]
    fn make_ipp_2() {
        test_helper_create(2);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4);
    }

    #[test]
    fn make_ipp_32() {
        test_helper_create(32);
    }

    #[test]
    fn make_ipp_64() {
        test_helper_create(64);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }
}

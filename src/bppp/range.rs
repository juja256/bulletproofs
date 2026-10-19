//! Range proofs (spec §5.1–5.2, paper §6.4): a reciprocal form circuit with the digits of
//! every value as poles and one table of multiplicities per radix.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};
use subtle::ConstantTimeEq;

use super::circuit::{CircuitProof, Slot};
use super::gens::BpppGens;
use super::reciprocal::{self, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness};
use super::sparse::SparseMatrix;
use super::transcript::BpppTranscript;
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// The digit layout of `[0, range)` in `base` (spec §5.1): `(weight, radix)` per digit, in
/// construction order. Needs `range >= 2`, `base >= 2`.
pub fn layout(range: u128, base: u64) -> Vec<(u128, u64)> {
    let b = base as u128;
    let mut out = Vec::new();
    let (mut s, mut p) = (0u128, 1u128);
    while s + (b - 1) * p <= range - 1 {
        out.push((p, base));
        s += (b - 1) * p;
        p *= b;
    }
    let mut r = range - 1 - s;
    if r >= b - 1 {
        let g = r / (b - 1);
        out.push((g, base));
        s += (b - 1) * g;
        r -= (b - 1) * g;
    }
    if r > 0 {
        out.push(if r <= s + 1 { (r, 2) } else { (1, r as u64 + 1) });
    }
    out
}

/// `n / d` for `d > 0`, `n < 2^127`, without data-dependent branches or the hardware divider.
fn ct_div(n: u128, d: u128) -> u128 {
    let (mut q, mut r) = (0u128, 0u128);
    for i in (0..128).rev() {
        r = (r << 1) | ((n >> i) & 1);
        let (diff, borrow) = r.overflowing_sub(d);
        let keep = (borrow as u128).wrapping_sub(1); // all ones when r >= d
        r = (diff & keep) | (r & !keep);
        q |= (keep & 1) << i;
    }
    q
}

/// The digits of `x` in `layout` (spec §5.1), in constant time with respect to `x`: from the
/// largest weight down, `d_j = max(0, ceil((x - M_j) / g_j))`.
pub(crate) fn decompose(x: u128, layout: &[(u128, u64)]) -> Vec<u64> {
    let mut order: Vec<usize> = (0..layout.len()).collect();
    order.sort_by_key(|&j| (layout[j].0, j));
    let mut below = vec![0u128; order.len()]; // M_j for each position
    let mut acc = 0u128;
    for (pos, &j) in order.iter().enumerate() {
        below[pos] = acc;
        acc += (layout[j].1 as u128 - 1) * layout[j].0;
    }
    let mut digits = vec![0u64; layout.len()];
    let mut rem = x;
    for pos in (0..order.len()).rev() {
        let j = order[pos];
        let g = layout[j].0;
        let diff = rem.wrapping_sub(below[pos]);
        let negative = diff >> 127; // 1 if rem < M_j (all values are < 2^66)
        let d = ct_div(diff.wrapping_add(g - 1), g) & negative.wrapping_sub(1);
        digits[j] = d as u64;
        rem = rem.wrapping_sub(d * g);
    }
    digits
}

/// The multiplicities `m_{r,s}`, `s = 1..r-1`, of the digits with radix `r` (constant time).
pub(crate) fn multiplicities(digits: &[(u64, u64)], r: u64) -> Vec<u64> {
    (1..r)
        .map(|s| digits.iter().filter(|(_, radix)| *radix == r).map(|(d, _)| d.ct_eq(&s).unwrap_u8() as u64).sum())
        .collect()
}

/// A range statement (spec §5.2): a base and `[A_i, B_i)` per value.
#[derive(Clone, Debug, PartialEq)]
pub struct RangeStatement {
    /// The base, `2..=256`.
    pub base: u64,
    /// `(A_i, B_i)` with `2 <= B_i - A_i` and `B_i <= 2^64`.
    pub ranges: Vec<(u64, u128)>,
}

/// The layout of a built range circuit.
pub(crate) struct RangeInfo {
    pub layouts: Vec<Vec<(u128, u64)>>,
    /// Distinct radices, ascending.
    tables: Vec<u64>,
    n_p: usize,
}

impl RangeInfo {
    /// The reciprocal witness for `values` with the given digits (one vector per value).
    pub fn witness(&self, values: &[u64], blindings: &[Scalar], digits: &[Vec<u64>]) -> ReciprocalWitness {
        let tagged: Vec<(u64, u64)> = digits
            .iter()
            .zip(&self.layouts)
            .flat_map(|(d, l)| d.iter().zip(l).map(|(d, (_, r))| (*d, *r)))
            .collect();
        let w_o = self.tables.iter().flat_map(|&r| multiplicities(&tagged, r)).map(Scalar::from).collect();
        ReciprocalWitness {
            w_d: tagged.iter().map(|(d, _)| Scalar::from(*d)).collect(),
            w_l: vec![],
            w_r: vec![],
            w_o,
            v: values.iter().map(|v| vec![Scalar::from(*v)]).collect(),
            s: blindings.to_vec(),
        }
    }
}

/// The tables and reciprocal rows of spec §5.2 for poles with the given radices; `pole_offset`
/// is the index of the first digit pole, `mult_col` the column of the first multiplicity.
pub(crate) fn table_rows(radices: &[u64], pole_offset: usize, n_mm: usize, mult_col: usize) -> (Vec<u64>, Vec<ReciprocalRow>) {
    let mut tables: Vec<u64> = radices.to_vec();
    tables.sort_unstable();
    tables.dedup();
    let mut rows = Vec::new();
    let mut col = mult_col;
    for &r in &tables {
        let mut terms: Vec<(usize, Scalar, Option<Scalar>)> = radices
            .iter()
            .enumerate()
            .filter(|(_, &x)| x == r)
            .map(|(p, _)| (n_mm + pole_offset + p, Scalar::ONE, None))
            .collect();
        for s in 1..r {
            terms.push((col, Scalar::ONE, Some(Scalar::ZERO)));
            terms.push((col, -Scalar::ONE, Some(Scalar::from(s))));
            col += 1;
        }
        let count = radices.iter().filter(|&&x| x == r).count() as u64;
        rows.push(ReciprocalRow { terms, consts: vec![(-Scalar::from(count), Some(Scalar::ZERO))] });
    }
    (tables, rows)
}

impl RangeStatement {
    /// Validate a statement.
    pub fn new(base: u64, ranges: Vec<(u64, u128)>) -> Result<Self, ProofError> {
        let ok = (2..=256).contains(&base)
            && !ranges.is_empty()
            && ranges.iter().all(|&(a, b)| b <= 1u128 << 64 && b >= a as u128 + 2);
        if ok {
            Ok(RangeStatement { base, ranges })
        } else {
            Err(ProofError::FormatError)
        }
    }

    /// The circuit of spec §5.2.
    pub(crate) fn circuit(&self) -> (ReciprocalCircuit, RangeInfo) {
        let layouts: Vec<Vec<(u128, u64)>> =
            self.ranges.iter().map(|&(a, b)| layout(b - a as u128, self.base)).collect();
        let radices: Vec<u64> = layouts.iter().flatten().map(|(_, r)| *r).collect();
        let n_p = radices.len();
        let n_mm = n_p;
        let mut tables: Vec<u64> = radices.clone();
        tables.sort_unstable();
        tables.dedup();
        let n_o: usize = tables.iter().map(|r| *r as usize - 1).sum();
        let inline = n_o <= n_p;
        let n_lin = if inline { 0 } else { n_o };
        let n_w = 2 * n_mm + n_o;
        let mut w_l = SparseMatrix::new(n_w);
        let mut pole = 0;
        for l in &layouts {
            let row: Vec<(usize, Scalar)> = l.iter().enumerate().map(|(j, (g, _))| (pole + j, -Scalar::from(*g))).collect();
            pole += l.len();
            w_l.push_row(row);
        }
        let mut w_n = SparseMatrix::new(n_w);
        for _ in 0..n_p {
            w_n.push_row(vec![]);
        }
        let (tables, recip) = table_rows(&radices, 0, n_mm, 2 * n_mm);
        let slot = if inline { Slot::NormO } else { Slot::LinL };
        let c = ReciprocalCircuit {
            n_p,
            n_m: 0,
            n_o,
            n_v: 1,
            n_lin,
            k: self.ranges.len(),
            w_n,
            a_n: vec![Scalar::ONE; n_p],
            w_m: SparseMatrix::new(n_w),
            a_m: vec![],
            w_l,
            a_l: self.ranges.iter().map(|&(a, _)| -Scalar::from(a)).collect(),
            recip,
            f_l: true,
            f_m: false,
            partition: (0..n_o).map(|t| (slot, t)).collect(),
        };
        (c, RangeInfo { layouts, tables, n_p })
    }

    /// The `BulletproofGens` capacity the proof needs.
    pub fn generators_capacity(&self) -> usize {
        let (c, _) = self.circuit();
        (c.n_p + c.n_m).max(c.n_lin + 6)
    }

    pub(crate) fn gens<'a>(&self, pc: &PedersenGens, bp: &'a BulletproofGens) -> Result<BpppGens<'a>, ProofError> {
        let (c, info) = self.circuit();
        BpppGens::new(pc, bp, c.n_lin, info.n_p)
    }
}

/// A BP++ range proof for several values (spec §5.2).
#[derive(Clone, Debug, PartialEq)]
pub struct RangeProof(pub(crate) CircuitProof);

impl RangeProof {
    /// Prove `values[i] in [A_i, B_i)` for commitments `values[i] B + blindings[i] B_blinding`;
    /// returns the proof and the commitments. Fails if a value is out of its range.
    pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
        st: &RangeStatement,
        pc: &PedersenGens,
        bp: &BulletproofGens,
        values: &[u64],
        blindings: &[Scalar],
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        if values.len() != st.ranges.len() || blindings.len() != st.ranges.len() {
            return Err(ProofError::FormatError);
        }
        if values.iter().zip(&st.ranges).any(|(&v, &(a, b))| v < a || v as u128 >= b) {
            return Err(ProofError::VerificationError);
        }
        let (c, info) = st.circuit();
        let g = st.gens(pc, bp)?;
        let digits: Vec<Vec<u64>> =
            values.iter().zip(&st.ranges).zip(&info.layouts).map(|((&v, &(a, _)), l)| decompose((v - a) as u128, l)).collect();
        let w = info.witness(values, blindings, &digits);
        let V: Vec<CompressedRistretto> = values.iter().zip(blindings).map(|(v, s)| pc.commit(Scalar::from(*v), *s).compress()).collect();
        transcript.domain_sep(b"bppp-range v1");
        let proof = reciprocal::prove(&c, &g, &V, &w, transcript, rng)?;
        Ok((RangeProof(proof), V))
    }

    /// Verify against the commitments `V`.
    pub fn verify<T: BpppTranscript>(
        &self,
        st: &RangeStatement,
        pc: &PedersenGens,
        bp: &BulletproofGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let (c, _) = st.circuit();
        let g = st.gens(pc, bp)?;
        transcript.domain_sep(b"bppp-range v1");
        reciprocal::verify(&self.0, &c, &g, V, transcript)
    }

    /// The proof bytes (spec §4.6).
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    /// Parse a proof for the statement `st`.
    pub fn from_bytes(bytes: &[u8], st: &RangeStatement) -> Result<Self, ProofError> {
        Ok(RangeProof(reciprocal::proof_from_bytes(bytes, &st.circuit().0)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand_chacha::rand_core::{RngCore, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    /// The set of digit sums of a layout, for small ranges.
    fn sums(layout: &[(u128, u64)]) -> Vec<u128> {
        let mut s = vec![0u128];
        for &(g, r) in layout {
            s = s.iter().flat_map(|x| (0..r as u128).map(move |d| x + d * g)).collect();
            s.sort_unstable();
            s.dedup();
        }
        s
    }

    #[test]
    fn layouts_are_exact() {
        for &b in &[2u64, 3, 4, 7, 16, 256] {
            for range in 2u128..300 {
                let l = layout(range, b);
                assert_eq!(sums(&l), (0..range).collect::<Vec<_>>(), "b = {}, B = {}", b, range);
            }
            for &range in &[1u128 << 64, (1u128 << 64) - 1, 1_000_000_000_000_000_000, 3 << 60] {
                let l = layout(range, b);
                let mut sorted = l.clone();
                sorted.sort_by_key(|x| x.0);
                let mut max = 0u128;
                for &(g, r) in &sorted {
                    assert!(g <= max + 1, "contiguity, b = {}, B = {}", b, range);
                    max += (r as u128 - 1) * g;
                }
                assert_eq!(max, range - 1);
            }
        }
        assert_eq!(layout(1 << 64, 16), (0..16).map(|j| (1u128 << (4 * j), 16)).collect::<Vec<_>>());
        assert_eq!(layout(10, 16), vec![(1, 10)]);
    }

    #[test]
    fn decompositions_are_valid() {
        let mut rng = ChaCha20Rng::seed_from_u64(40);
        for &b in &[2u64, 3, 16, 256] {
            for &range in &[2u128, 10, 255, 256, 1000, 4097, 1 << 64] {
                let l = layout(range, b);
                let xs: Vec<u128> = if range <= 4097 {
                    (0..range).collect()
                } else {
                    vec![0, 1, range - 1, range / 3, (rng.next_u64() as u128) % range]
                };
                for x in xs {
                    let d = decompose(x, &l);
                    assert!(d.iter().zip(&l).all(|(d, (_, r))| *d < *r), "digit range");
                    assert_eq!(d.iter().zip(&l).map(|(d, (g, _))| *d as u128 * g).sum::<u128>(), x);
                }
            }
        }
    }

    #[test]
    fn ct_div_matches_division() {
        let mut rng = ChaCha20Rng::seed_from_u64(41);
        for _ in 0..2000 {
            let n = ((rng.next_u64() as u128) << 1) | (rng.next_u32() as u128 & 1);
            let d = (rng.next_u64() as u128 % (1u128 << 64)).max(1);
            assert_eq!(ct_div(n, d), n / d);
        }
        assert_eq!(ct_div(u64::MAX as u128 * 2, 1 << 64), 1);
    }

    fn gens(st: &RangeStatement) -> (PedersenGens, BulletproofGens) {
        (PedersenGens::default(), BulletproofGens::new(st.generators_capacity(), 1))
    }

    #[test]
    fn range_proofs_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let cases: Vec<(u64, Vec<(u64, u128)>, Vec<u64>)> = vec![
            (16, vec![(0, 1 << 64)], vec![0]),
            (16, vec![(0, 1 << 64)], vec![u64::MAX]),
            (2, vec![(0, 1 << 64)], vec![0x0123_4567_89ab_cdef]),
            (16, vec![(1000, 1000 + 4096)], vec![1000 + 4095]),
            (16, vec![(1000, 2000)], vec![1999]),
            (16, vec![(5, 15)], vec![9]),
            (4, vec![(7, 9)], vec![8]),
            (16, vec![(0, 1 << 64), (10, 20), (1 << 40, (1 << 40) + 4097)], vec![12345, 19, (1 << 40) + 4096]),
        ];
        for (base, ranges, values) in cases {
            let st = RangeStatement::new(base, ranges.clone()).unwrap();
            let (pc, bp) = gens(&st);
            let blindings: Vec<Scalar> = values.iter().map(|_| Scalar::random(&mut rng)).collect();
            let (proof, V) =
                RangeProof::prove(&st, &pc, &bp, &values, &blindings, &mut Transcript::new(b"r"), &mut rng)
                    .unwrap_or_else(|e| panic!("base {} ranges {:?}: {:?}", base, ranges, e));
            for (i, v) in values.iter().enumerate() {
                assert_eq!(V[i], pc.commit(Scalar::from(*v), blindings[i]).compress());
            }
            let parsed = RangeProof::from_bytes(&proof.to_bytes(), &st).unwrap();
            assert_eq!(parsed, proof);
            proof.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"r")).unwrap();
            assert!(proof.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"x")).is_err());
            let mut swapped = V.clone();
            swapped[0] = pc.commit(Scalar::from(values[0]) + Scalar::ONE, blindings[0]).compress();
            assert!(proof.verify(&st, &pc, &bp, &swapped, &mut Transcript::new(b"r")).is_err());
        }
    }

    /// 64 bits in base 16 with inline multiplicities: 13 group elements and scalars (paper: 416 B).
    #[test]
    fn size_of_a_64_bit_proof() {
        let mut rng = ChaCha20Rng::seed_from_u64(43);
        let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
        let (pc, bp) = gens(&st);
        let (proof, _) = RangeProof::prove(&st, &pc, &bp, &[42], &[Scalar::ONE], &mut Transcript::new(b"r"), &mut rng)
            .unwrap();
        assert_eq!(proof.to_bytes().len(), 416);
    }

    #[test]
    fn out_of_range_values_are_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(44);
        let st = RangeStatement::new(16, vec![(1000, 2000)]).unwrap();
        let (pc, bp) = gens(&st);
        for &v in &[999u64, 2000, 0, u64::MAX] {
            assert!(RangeProof::prove(&st, &pc, &bp, &[v], &[Scalar::ONE], &mut Transcript::new(b"r"), &mut rng).is_err());
        }
        // a digit outside its radix, with the linear row holding: v = 2000 as digits of
        // [0, 1000) with the top digit one too large; the prover's check refuses, and a proof
        // made without it does not verify
        let (c, info) = st.circuit();
        let layout = &info.layouts[0];
        let mut digits = decompose(999, layout);
        let top = (0..layout.len()).max_by_key(|&j| (layout[j].0, j)).unwrap();
        digits[top] += 1001 / layout[top].0 as u64; // overshoot the radix of the top digit
        let x: u128 = digits.iter().zip(layout).map(|(d, (g, _))| *d as u128 * g).sum();
        let v = 1000 + x as u64;
        let w = info.witness(&[v], &[Scalar::ONE], &[digits]);
        let g = st.gens(&pc, &bp).unwrap();
        let V = vec![pc.commit(Scalar::from(v), Scalar::ONE).compress()];
        assert!(!c.is_satisfied(&w, Scalar::from(77u64)));
        let mut t = Transcript::new(b"r");
        t.append_message(b"dom-sep", b"bppp-range v1");
        let proof = reciprocal::prove_impl(&c, &g, &V, &w, &mut t, &mut rng, false).unwrap();
        assert!(RangeProof(proof).verify(&st, &pc, &bp, &V, &mut Transcript::new(b"r")).is_err());
    }

    #[test]
    fn statements_are_validated() {
        assert!(RangeStatement::new(1, vec![(0, 10)]).is_err());
        assert!(RangeStatement::new(257, vec![(0, 10)]).is_err());
        assert!(RangeStatement::new(16, vec![]).is_err());
        assert!(RangeStatement::new(16, vec![(5, 6)]).is_err(), "B - A = 1");
        assert!(RangeStatement::new(16, vec![(5, 5)]).is_err());
        assert!(RangeStatement::new(16, vec![(0, (1 << 64) + 1)]).is_err());
        assert!(RangeStatement::new(16, vec![(0, 1 << 64)]).is_ok());
    }
}

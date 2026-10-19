//! Multi-asset confidential transactions (spec §5.3, paper §6.5): per asset type the inputs
//! and outputs balance, and every output amount is in `[0, 2^64)`.

use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand_core::{CryptoRng, RngCore};

use super::circuit::{CircuitProof, Slot};
use super::gens::BpppGens;
use super::range::{decompose, layout, multiplicities, table_rows};
use super::reciprocal::{self, ReciprocalCircuit, ReciprocalRow, ReciprocalWitness};
use super::sparse::SparseMatrix;
use super::transcript::BpppTranscript;
use crate::errors::ProofError;
use crate::{BulletproofGens, PedersenGens};

/// An input or output: amount, asset type (a scalar, e.g. a hash of the asset id) and blinding.
/// Committed as `amount B + blinding B_blinding + asset H_7` (spec §5.3). `Debug` hides it.
#[derive(Clone, Copy)]
pub struct MactEntry {
    /// The amount.
    pub amount: u64,
    /// The asset type.
    pub asset: Scalar,
    /// The blinding.
    pub blinding: Scalar,
}

impl core::fmt::Debug for MactEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MactEntry { .. }")
    }
}

/// The shape of a transaction: numbers of inputs and outputs and the base of the range proofs.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MactStatement {
    /// The base, `2..=256`.
    pub base: u64,
    /// Number of inputs.
    pub n_in: usize,
    /// Number of outputs.
    pub n_out: usize,
}

pub(crate) struct MactInfo {
    layout: Vec<(u128, u64)>,
    tables: Vec<u64>,
}

impl MactStatement {
    /// Validate a statement.
    pub fn new(base: u64, n_in: usize, n_out: usize) -> Result<Self, ProofError> {
        if !(2..=256).contains(&base) || n_in.checked_add(n_out).map_or(true, |k| k == 0) {
            return Err(ProofError::FormatError);
        }
        Ok(MactStatement { base, n_in, n_out })
    }

    fn k(&self) -> usize {
        self.n_in + self.n_out
    }

    /// The circuit of spec §5.3.
    pub(crate) fn circuit(&self) -> (ReciprocalCircuit, MactInfo) {
        let k = self.k();
        let layout = layout(1u128 << 64, self.base);
        let digit_radices: Vec<u64> = (0..self.n_out).flat_map(|_| layout.iter().map(|(_, r)| *r)).collect();
        let n_p = k + digit_radices.len();
        let n_mm = n_p;
        let mut tables: Vec<u64> = digit_radices.clone();
        tables.sort_unstable();
        tables.dedup();
        let n_mult: usize = tables.iter().map(|r| *r as usize - 1).sum();
        let inline = n_mult <= n_p;
        let n_lin = 1.max(k).max(if inline { 0 } else { n_mult });
        let n_o = k + n_mult;
        let n_w = 2 * n_mm + n_o;
        let copy = |i: usize| 2 * n_mm + i;
        let mut w_n = SparseMatrix::new(n_w);
        for i in 0..k {
            let sign = if i < self.n_in { Scalar::ONE } else { -Scalar::ONE };
            w_n.push_row(vec![(copy(i), sign)]);
        }
        for _ in k..n_p {
            w_n.push_row(vec![]);
        }
        let mut w_l = SparseMatrix::new(n_w);
        for i in 0..k {
            w_l.push_row(vec![(copy(i), -Scalar::ONE)]);
            w_l.push_row(vec![(i, -Scalar::ONE)]);
        }
        for j in 0..self.n_out {
            let first = k + j * layout.len();
            let mut row: Vec<(usize, Scalar)> =
                layout.iter().enumerate().map(|(d, (g, _))| (first + d, -Scalar::from(*g))).collect();
            row.push((copy(self.n_in + j), Scalar::ONE));
            w_l.push_row(row);
        }
        let balance = ReciprocalRow { terms: (0..k).map(|i| (n_mm + i, Scalar::ONE, None)).collect(), consts: vec![] };
        let (tables, table_recip) = table_rows(&digit_radices, k, n_mm, 2 * n_mm + k);
        let mut recip = vec![balance];
        recip.extend(table_recip);
        let mult_slot = if inline { Slot::NormO } else { Slot::LinL };
        let partition = (0..k).map(|i| (Slot::LinO, i)).chain((0..n_mult).map(|t| (mult_slot, t))).collect();
        let c = ReciprocalCircuit {
            n_p,
            n_m: 0,
            n_o,
            n_v: 2,
            n_lin,
            k,
            w_n,
            a_n: (0..n_p).map(|p| if p < k { Scalar::ZERO } else { Scalar::ONE }).collect(),
            w_m: SparseMatrix::new(n_w),
            a_m: vec![],
            w_l,
            a_l: vec![Scalar::ZERO; 2 * k + self.n_out],
            recip,
            f_l: true,
            f_m: false,
            partition,
        };
        (c, MactInfo { layout, tables })
    }

    /// The `BulletproofGens` capacity the proof needs.
    pub fn generators_capacity(&self) -> usize {
        let (c, _) = self.circuit();
        (c.n_p + c.n_m).max(c.n_lin + 6)
    }

    pub(crate) fn gens<'a>(&self, pc: &PedersenGens, bp: &'a BulletproofGens) -> Result<BpppGens<'a>, ProofError> {
        let (c, _) = self.circuit();
        BpppGens::new(pc, bp, c.n_lin, c.n_p + c.n_m)
    }
}

impl MactInfo {
    /// The reciprocal witness for the entries (inputs first) with the given output digits.
    pub(crate) fn witness(&self, entries: &[MactEntry], out_digits: &[Vec<u64>]) -> ReciprocalWitness {
        let tagged: Vec<(u64, u64)> =
            out_digits.iter().flat_map(|d| d.iter().zip(&self.layout).map(|(d, (_, r))| (*d, *r))).collect();
        ReciprocalWitness {
            w_d: entries.iter().map(|e| e.asset).chain(tagged.iter().map(|(d, _)| Scalar::from(*d))).collect(),
            w_l: vec![],
            w_r: vec![],
            w_o: entries
                .iter()
                .map(|e| Scalar::from(e.amount))
                .chain(self.tables.iter().flat_map(|&r| multiplicities(&tagged, r)).map(Scalar::from))
                .collect(),
            v: entries.iter().map(|e| vec![Scalar::from(e.amount), e.asset]).collect(),
            s: entries.iter().map(|e| e.blinding).collect(),
        }
    }
}

/// A BP++ multi-asset transaction proof (spec §5.3).
#[derive(Clone, Debug, PartialEq)]
pub struct MactProof(pub(crate) CircuitProof);

impl MactProof {
    /// Prove that `inputs` and `outputs` balance per asset type and that the outputs are in
    /// range; returns the proof and the commitments (inputs, then outputs). Fails if they do
    /// not balance.
    pub fn prove<T: BpppTranscript, R: RngCore + CryptoRng>(
        st: &MactStatement,
        pc: &PedersenGens,
        bp: &BulletproofGens,
        inputs: &[MactEntry],
        outputs: &[MactEntry],
        transcript: &mut T,
        rng: &mut R,
    ) -> Result<(MactProof, Vec<CompressedRistretto>), ProofError> {
        if inputs.len() != st.n_in || outputs.len() != st.n_out {
            return Err(ProofError::FormatError);
        }
        let (c, info) = st.circuit();
        let g = st.gens(pc, bp)?;
        let entries: Vec<MactEntry> = inputs.iter().chain(outputs).copied().collect();
        let out_digits: Vec<Vec<u64>> = outputs.iter().map(|e| decompose(e.amount as u128, &info.layout)).collect();
        let w = info.witness(&entries, &out_digits);
        let V: Vec<CompressedRistretto> =
            entries.iter().map(|e| g.commit_input(&[Scalar::from(e.amount), e.asset], e.blinding).compress()).collect();
        transcript.domain_sep(b"bppp-mact v1");
        let proof = reciprocal::prove(&c, &g, &V, &w, transcript, rng)?;
        Ok((MactProof(proof), V))
    }

    /// Verify against the commitments `V` (inputs, then outputs).
    pub fn verify<T: BpppTranscript>(
        &self,
        st: &MactStatement,
        pc: &PedersenGens,
        bp: &BulletproofGens,
        V: &[CompressedRistretto],
        transcript: &mut T,
    ) -> Result<(), ProofError> {
        let (c, _) = st.circuit();
        let g = st.gens(pc, bp)?;
        transcript.domain_sep(b"bppp-mact v1");
        reciprocal::verify(&self.0, &c, &g, V, transcript)
    }

    /// The proof bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    /// Parse a proof for the statement `st`.
    pub fn from_bytes(bytes: &[u8], st: &MactStatement) -> Result<Self, ProofError> {
        Ok(MactProof(reciprocal::proof_from_bytes(bytes, &st.circuit().0)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn entry(amount: u64, asset: u64, rng: &mut ChaCha20Rng) -> MactEntry {
        MactEntry { amount, asset: Scalar::from(asset) * Scalar::from(0x1234_5678u64), blinding: Scalar::random(rng) }
    }

    fn run(base: u64, ins: &[(u64, u64)], outs: &[(u64, u64)], rng: &mut ChaCha20Rng) -> Result<(), ProofError> {
        let st = MactStatement::new(base, ins.len(), outs.len())?;
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(st.generators_capacity(), 1);
        let inputs: Vec<MactEntry> = ins.iter().map(|&(a, t)| entry(a, t, rng)).collect();
        let outputs: Vec<MactEntry> = outs.iter().map(|&(a, t)| entry(a, t, rng)).collect();
        let (proof, V) = MactProof::prove(&st, &pc, &bp, &inputs, &outputs, &mut Transcript::new(b"m"), rng)?;
        assert_eq!(MactProof::from_bytes(&proof.to_bytes(), &st).unwrap(), proof);
        proof.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m"))
    }

    #[test]
    fn balanced_transactions_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(50);
        run(16, &[(100, 1), (50, 2)], &[(70, 1), (30, 1), (50, 2)], &mut rng).unwrap();
        run(16, &[(u64::MAX, 7)], &[(u64::MAX, 7)], &mut rng).unwrap();
        run(4, &[(10, 1), (20, 1)], &[(5, 1), (25, 1)], &mut rng).unwrap();
        run(16, &[(0, 3)], &[], &mut rng).unwrap();
        run(16, &[(9, 1), (9, 2)], &[(9, 2), (9, 1)], &mut rng).unwrap();
    }

    /// Unbalanced (per asset) transactions: the prover refuses, and a proof made without the
    /// check does not verify.
    #[test]
    fn unbalanced_transactions_are_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(51);
        for (ins, outs) in [
            (vec![(100u64, 1u64)], vec![(101u64, 1u64)]),
            (vec![(100, 1), (50, 2)], vec![(50, 1), (100, 2)]), // totals balance, types do not
            (vec![(10, 1)], vec![(10, 2)]),
        ] {
            assert!(run(16, &ins, &outs, &mut rng).is_err());
            let st = MactStatement::new(16, ins.len(), outs.len()).unwrap();
            let pc = PedersenGens::default();
            let bp = BulletproofGens::new(st.generators_capacity(), 1);
            let g = st.gens(&pc, &bp).unwrap();
            let (c, info) = st.circuit();
            let entries: Vec<MactEntry> = ins.iter().chain(&outs).map(|&(a, t)| entry(a, t, &mut rng)).collect();
            let digits: Vec<Vec<u64>> = outs.iter().map(|&(a, _)| decompose(a as u128, &info.layout)).collect();
            let w = info.witness(&entries, &digits);
            let V: Vec<CompressedRistretto> =
                entries.iter().map(|e| g.commit_input(&[Scalar::from(e.amount), e.asset], e.blinding).compress()).collect();
            let mut t = Transcript::new(b"m");
            t.append_message(b"dom-sep", b"bppp-mact v1");
            let proof = reciprocal::prove_impl(&c, &g, &V, &w, &mut t, &mut rng, false).unwrap();
            assert!(MactProof(proof).verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).is_err());
        }
    }

    /// The circuits built from the statements equal the reference's field by field, honest
    /// witnesses match, and the proofs reproduce `tests/vectors/bppp/mact.json`.
    #[test]
    fn matches_reference_vectors() {
        use crate::bppp::testutil::{self, int, sc};
        let file: serde_json::Value = serde_json::from_str(include_str!("../../tests/vectors/bppp/mact.json")).unwrap();
        for case in file["cases"].as_array().unwrap() {
            let name = case["name"].as_str().unwrap();
            let u = |k: &str| case[k].as_u64().unwrap() as usize;
            let st = MactStatement::new(case["base"].as_u64().unwrap(), u("n_in"), u("n_out")).unwrap();
            let (c, info) = st.circuit();
            assert_eq!(c, testutil::recip_circuit(case), "{}: circuit", name);
            let w = testutil::recip_witness(case);
            if case["satisfied"].as_bool().unwrap() {
                let parse = |v: &serde_json::Value| -> Vec<MactEntry> {
                    v.as_array()
                        .unwrap()
                        .iter()
                        .map(|e| MactEntry { amount: int(&e["amount"]) as u64, asset: sc(&e["asset"]), blinding: sc(&e["blinding"]) })
                        .collect()
                };
                let (ins, outs) = (parse(&case["inputs"]), parse(&case["outputs"]));
                let entries: Vec<MactEntry> = ins.iter().chain(&outs).copied().collect();
                let digits: Vec<Vec<u64>> = outs.iter().map(|e| decompose(e.amount as u128, &info.layout)).collect();
                let ours = info.witness(&entries, &digits);
                assert!(
                    ours.w_d == w.w_d && ours.w_o == w.w_o && ours.v == w.v && ours.s == w.s,
                    "{}: witness",
                    name
                );
            }
            testutil::run_recip_case(case, &c, &w);
        }
    }

    /// An output with a digit outside its radix (a "negative" amount in disguise) does not verify.
    #[test]
    fn output_digit_out_of_range_is_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(52);
        let st = MactStatement::new(16, 1, 2).unwrap();
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(st.generators_capacity(), 1);
        let g = st.gens(&pc, &bp).unwrap();
        let (c, info) = st.circuit();
        // in 46 = out 30 + out 16, balanced, but the second output is written with the digit
        // 16 in the lowest place, outside radix 16
        let entries = [entry(46, 1, &mut rng), entry(30, 1, &mut rng), entry(16, 1, &mut rng)];
        let mut d2 = vec![0u64; info.layout.len()];
        d2[0] = 16;
        let digits = vec![decompose(30, &info.layout), d2];
        let w = info.witness(&entries, &digits);
        assert!(!c.is_satisfied(&w, Scalar::from(99u64)));
        let V: Vec<CompressedRistretto> =
            entries.iter().map(|e| g.commit_input(&[Scalar::from(e.amount), e.asset], e.blinding).compress()).collect();
        let mut t = Transcript::new(b"m");
        t.append_message(b"dom-sep", b"bppp-mact v1");
        let proof = reciprocal::prove_impl(&c, &g, &V, &w, &mut t, &mut rng, false).unwrap();
        assert!(MactProof(proof).verify(&st, &pc, &bp, &V, &mut Transcript::new(b"m")).is_err());
    }
}

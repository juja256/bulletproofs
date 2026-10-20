//! Tests of `bppp::reciprocal`.

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
    (PedersenGens::default(), BulletproofGens::new(c.gens_capacity(), 1))
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
                let g = c.gens(&pc, &bp).unwrap();
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
        let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
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
/// the prover refuses and an unchecked proof does not verify. A base-16 packing of
/// unbounded components would accept the first.
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
        let g = c.gens(&pc, &bp).unwrap();
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
    let g = c.gens(&pc, &bp).unwrap();
    let gr = BpppGens::new(&pc, &bp, r.n_lin, r.n_p + r.n_m).unwrap();
    let Vr = inputs(&gr, &rw);
    let mut rng = ChaCha20Rng::seed_from_u64(9);
    let p1 = prove(&c, &g, &[], &w, &mut Transcript::new(b"b"), &mut rng).unwrap();
    let p2 = prove(&r, &gr, &Vr, &rw, &mut Transcript::new(b"b"), &mut rng).unwrap();
    let run = |p1: &CircuitProof| {
        let mut b = crate::bppp::BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(1));
        b.add_reciprocal(&ReciprocalProof(p1.clone()), &c, &[], &mut Transcript::new(b"b"))?;
        b.add_reciprocal(&ReciprocalProof(p2.clone()), &r, &Vr, &mut Transcript::new(b"b"))?;
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

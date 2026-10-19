//! Tuple poles (spec §4.1–4.7), from the review of phase 7b: numerators and ordinary rows
//! that read a tuple pole, the two-phase prover with tuple poles, v2 from long public poles
//! alone, and malformed v2 circuits (errors, no panics).
use alloc::vec;
use alloc::vec::Vec;

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use super::circuit::Slot;
use super::gens::BpppGens;
use super::reciprocal::*;
use super::sparse::SparseMatrix;
use crate::{BulletproofGens, PedersenGens};

fn s(x: u64) -> Scalar {
    Scalar::from(x)
}

/// Two tuple poles with the same tuple (a, b) in w_O; numerators of both poles read w_D,0 (a
/// tuple pole); an ordinary linear row w_D,0 - w_D,1 = 0; one ordinary gate w_L w_R = w_O[2]
/// (late w_R for the two-phase prover). Row: w_P,0 - w_P,1 = 0.
fn circuit(a: Scalar, b: Scalar) -> (ReciprocalCircuit, ReciprocalWitness) {
    let (n_p, n_m) = (2usize, 1usize);
    let n_mm = n_p + n_m;
    let n_o = 3; // a, b, product output
    let n_lin = 0;
    let n_w = 2 * n_mm + n_o;
    let col_o = |e: usize| 2 * n_mm + e;
    let mut w_n = SparseMatrix::new(n_w);
    w_n.push_row(vec![(0, Scalar::ONE)]); // num_0 = w_D,0
    w_n.push_row(vec![(0, Scalar::ONE)]); // num_1 = w_D,0
    let mut w_m = SparseMatrix::new(n_w);
    w_m.push_row(vec![(col_o(2), Scalar::ONE)]);
    let mut w_l = SparseMatrix::new(n_w);
    w_l.push_row(vec![(0, Scalar::ONE), (1, -Scalar::ONE)]);
    let comp = |e: usize| Component { terms: vec![(col_o(e), Scalar::ONE)], constant: Scalar::ZERO };
    let c = ReciprocalCircuit {
        n_p,
        n_m,
        n_o,
        n_v: 1,
        n_lin,
        k: 0,
        w_n,
        a_n: vec![Scalar::ZERO; 2],
        w_m,
        a_m: vec![Scalar::ZERO],
        w_l,
        a_l: vec![Scalar::ZERO],
        recip: vec![ReciprocalRow { terms: vec![(n_mm, Scalar::ONE, None), (n_mm + 1, -Scalar::ONE, None)], consts: vec![] }],
        tuples: vec![
            TuplePole { pole: 0, components: vec![comp(0), comp(1)] },
            TuplePole { pole: 1, components: vec![comp(0), comp(1)] },
        ],
        f_l: false,
        f_m: false,
        partition: (0..n_o).map(|e| (Slot::NormO, e)).collect(),
    };
    let w = ReciprocalWitness { w_d: vec![s(7), s(8)], w_l: vec![s(3)], w_r: vec![s(5)], w_o: vec![a, b, s(15)], v: vec![], s: vec![] };
    (c, w)
}

fn gens(c: &ReciprocalCircuit) -> (PedersenGens, BulletproofGens) {
    let _ = c;
    (PedersenGens::default(), BulletproofGens::new(64, 1))
}
fn mk<'a>(c: &ReciprocalCircuit, g: &'a (PedersenGens, BulletproofGens)) -> BpppGens<'a> {
    c.gens(&g.0, &g.1).unwrap()
}

#[test]
fn numerators_and_rows_reading_tuple_poles() {
    let (c, w) = circuit(s(3), s(5));
    c.check().unwrap();
    assert!(c.uses_eta());
    assert!(c.is_satisfied(&w, s(11), s(13)));
    let gg = gens(&c);
    let g = mk(&c, &gg);
    let p = prove(&c, &g, &[], &w, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    verify(&p, &c, &g, &[], &mut Transcript::new(b"p")).unwrap();
    // two-phase prover: w_R from the callback
    let mut w0 = w.clone();
    w0.w_r = vec![Scalar::ZERO];
    let late = |_alpha: Scalar, w_p: &[Scalar]| {
        assert_eq!(w_p.len(), 2);
        Ok(LateWitness { w_r: vec![s(5)], w_o_late: vec![] })
    };
    let p2 = prove_two_phase(&c, &g, &[], &w0, late, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    assert_eq!(p, p2, "same proof as the one-phase prover");
    verify(&p2, &c, &g, &[], &mut Transcript::new(b"p")).unwrap();
}

#[test]
fn malformed_circuits_do_not_panic() {
    let (c, w) = circuit(s(3), s(5));
    let gg = gens(&c);
    let g = mk(&c, &gg);
    let p = prove(&c, &g, &[], &w, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    let mut bads: Vec<ReciprocalCircuit> = Vec::new();
    let mut x = c.clone();
    x.recip[0].terms[0].2 = Some(Pole(vec![]));
    bads.push(x);
    let mut x = c.clone();
    x.recip[0].consts.push((Scalar::ONE, Some(Pole(vec![]))));
    bads.push(x);
    let mut x = c.clone();
    x.tuples[0].components[0].terms[0].0 = usize::MAX;
    bads.push(x);
    let mut x = c.clone();
    x.tuples[0].pole = usize::MAX;
    bads.push(x);
    let mut x = c.clone();
    x.tuples[1].pole = 1 << 40;
    bads.push(x);
    let mut x = c.clone();
    x.n_p = 0;
    bads.push(x);
    let mut x = c.clone();
    x.n_o = usize::MAX;
    bads.push(x);
    let mut x = c.clone();
    x.n_p = usize::MAX / 2;
    bads.push(x);
    let mut x = c.clone();
    x.tuples.push(TuplePole { pole: 1, components: vec![] });
    bads.push(x);
    let mut x = c.clone();
    x.partition.clear();
    bads.push(x);
    let mut x = c.clone();
    x.tuples.pop(); // pole 1 free, in the row of the tuple pole 0
    bads.push(x);
    for (i, b) in bads.iter().enumerate() {
        let _ = b.uses_eta();
        let _ = b.digest();
        assert!(b.check().is_err(), "{}", i);
        assert!(!b.is_satisfied(&w, s(1), s(2)), "{}", i);
        assert!(verify(&p, b, &g, &[], &mut Transcript::new(b"p")).is_err(), "{}", i);
        assert!(prove(b, &g, &[], &w, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).is_err(), "{}", i);
    }
    // wrong witness lengths
    let mut w2 = w.clone();
    w2.w_o.pop();
    assert!(prove(&c, &g, &[], &w2, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).is_err());
    assert!(!c.is_satisfied(&w2, s(1), s(2)));
}

/// v2 without tuple poles: a free pole in its own row, a public pole polynomial of length 2 in
/// another (constants only, they cancel), proves and verifies; a v1 twin (length-1 poles) has another digest and
/// transcript.
#[test]
fn long_public_poles_without_tuples() {
    let (n_p, n_m) = (1usize, 1usize);
    let n_mm = n_p + n_m;
    let n_o = 1;
    let n_w = 2 * n_mm + n_o;
    let mut w_n = SparseMatrix::new(n_w);
    w_n.push_row(vec![]);
    let mut w_m = SparseMatrix::new(n_w);
    w_m.push_row(vec![(2 * n_mm, Scalar::ONE)]);
    let long = Pole(vec![s(4), s(9)]);
    let c = ReciprocalCircuit {
        n_p,
        n_m,
        n_o,
        n_v: 1,
        n_lin: 0,
        k: 0,
        w_n,
        a_n: vec![Scalar::ONE],
        w_m,
        a_m: vec![Scalar::ZERO],
        w_l: SparseMatrix::new(n_w),
        a_l: vec![],
        // the free pole in a v1-style row; the long poles in a public-only row (spec §4.1:
        // they must not share a row with a free pole)
        recip: vec![
            ReciprocalRow { terms: vec![(n_mm, Scalar::ONE, None)], consts: vec![(-Scalar::ONE, Some(s(6).into()))] },
            ReciprocalRow { terms: vec![], consts: vec![(s(2), Some(long.clone())), (-s(2), Some(long))] },
        ],
        tuples: vec![],
        f_l: false,
        f_m: false,
        partition: vec![(Slot::NormO, 0)],
    };
    c.check().unwrap();
    assert!(c.uses_eta());
    let w = ReciprocalWitness { w_d: vec![s(6)], w_l: vec![s(3)], w_r: vec![s(5)], w_o: vec![s(15)], v: vec![], s: vec![] };
    assert!(c.is_satisfied(&w, s(11), s(13)));
    let gg = gens(&c);
    let g = mk(&c, &gg);
    let p = prove(&c, &g, &[], &w, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    verify(&p, &c, &g, &[], &mut Transcript::new(b"p")).unwrap();
    // the v1 twin: a length-1 pole with the same value at eta = 0 is another circuit
    let mut v1 = c.clone();
    v1.recip[1].consts[0].1 = Some(s(4).into());
    v1.recip[1].consts[1].1 = Some(s(4).into());
    assert!(!v1.uses_eta());
    assert_ne!(v1.digest(), c.digest());
    assert!(verify(&p, &v1, &g, &[], &mut Transcript::new(b"p")).is_err());
    let p1 = prove(&v1, &g, &[], &w, &mut Transcript::new(b"p"), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    assert!(verify(&p1, &c, &g, &[], &mut Transcript::new(b"p")).is_err());
}

//! The README's table of the curves: proof size, prove and verify times (median of runs) for a
//! 64-bit range proof (BP and BP++) and R1CS circuits of 2^10 and 2^14 multiplications on both
//! backends, over ristretto255 and secp256k1.
//!
//! `cargo run --release --example curves_table`
//! (add `parallel` for multi-threaded numbers).

use std::time::Instant;

use bulletproofs::bppp::{RangeProof as BpppRangeProof, RangeStatement};
use bulletproofs::curve::ff::Field;
use bulletproofs::curve::{Curve, Ristretto, Secp256k1};
use bulletproofs::r1cs::{Backend, ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

fn median(mut f: impl FnMut(), runs: usize) -> f64 {
    let mut t: Vec<f64> = (0..runs)
        .map(|_| {
            let s = Instant::now();
            f();
            s.elapsed().as_secs_f64()
        })
        .collect();
    t.sort_by(|a, b| a.partial_cmp(b).unwrap());
    t[runs / 2]
}

fn fmt(s: f64) -> String {
    if s < 1e-3 {
        format!("{:.0} µs", s * 1e6)
    } else if s < 1.0 {
        format!("{:.2} ms", s * 1e3)
    } else {
        format!("{:.2} s", s)
    }
}

fn row(curve: &str, proof: &str, backend: &str, size: usize, prove: f64, verify: f64) {
    println!("| {} | {} | {} | {} B | {} | {} |", curve, proof, backend, size, fmt(prove), fmt(verify));
}

fn range<C: Curve>(runs: usize) {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let pc = PedersenGens::<C>::default();
    let bp = BulletproofGens::<C>::new(64, 1);
    let b = C::Scalar::random(&mut rng);
    let (proof, v) = RangeProof::<C>::prove_single_with_rng(&bp, &pc, &mut Transcript::new(b"t"), 7, &b, 64, &mut rng).unwrap();
    let prove = median(|| drop(RangeProof::<C>::prove_single_with_rng(&bp, &pc, &mut Transcript::new(b"t"), 7, &b, 64, &mut rng)), runs);
    let verify = median(|| proof.verify_single(&bp, &pc, &mut Transcript::new(b"t"), &v, 64).unwrap(), runs);
    row(C::NAME, "range 64 bits", "BP", proof.to_bytes().len(), prove, verify);

    let st = RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
    let bp = BulletproofGens::<C>::new(st.generators_capacity(), 1);
    let (proof, v) = BpppRangeProof::<C>::prove(&st, &pc, &bp, &[7], &[b], &mut Transcript::new(b"t"), &mut rng).unwrap();
    let prove = median(|| drop(BpppRangeProof::<C>::prove(&st, &pc, &bp, &[7], &[b], &mut Transcript::new(b"t"), &mut rng)), runs);
    let verify = median(|| proof.verify(&st, &pc, &bp, &v, &mut Transcript::new(b"t")).unwrap(), runs);
    row(C::NAME, "range 64 bits", "BP++", proof.to_bytes().len(), prove, verify);
}

/// A chain of multiplications `x_{i+1} = x_i * y_i`, `x_0` committed: the prover passes the
/// pairs `(x_i, y_i)`, the verifier `None`.
fn chain<C: Curve, CS: ConstraintSystem<C::Scalar>>(cs: &mut CS, x0: Variable, n: usize, pairs: Option<&[(C::Scalar, C::Scalar)]>) {
    let mut prev: LinearCombination<C::Scalar> = x0.into();
    for i in 0..n {
        let (l, _, o) = cs.allocate_multiplier(pairs.map(|p| p[i])).unwrap();
        cs.constrain(prev - l);
        prev = o.into();
    }
}

fn r1cs<C: Curve>(n: usize, backend: Backend, runs: usize) {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let pc = PedersenGens::<C>::default();
    let bp = BulletproofGens::<C>::new(2 * n + 64, 1);
    let mut x = C::Scalar::from(3u64);
    let pairs: Vec<(C::Scalar, C::Scalar)> = (0..n)
        .map(|_| {
            let y = C::Scalar::random(&mut rng);
            let p = (x, y);
            x *= y;
            p
        })
        .collect();
    let blinding = C::Scalar::random(&mut rng);
    let prove_once = |rng: &mut ChaCha20Rng| {
        let mut t = Transcript::new(b"c");
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(backend);
        let (c, x0) = p.commit(pairs[0].0, blinding);
        chain::<C, _>(&mut p, x0, n, Some(&pairs));
        (p.prove_with_rng(&bp, rng).unwrap(), c)
    };
    let (proof, c) = prove_once(&mut rng);
    let prove = median(|| drop(prove_once(&mut rng)), runs);
    let verify = median(
        || {
            let mut t = Transcript::new(b"c");
            let mut v = Verifier::<_, C>::new(&mut t);
            v.set_backend(backend);
            let x0 = v.commit(c);
            chain::<C, _>(&mut v, x0, n, None);
            v.verify(&proof, &pc, &bp).unwrap()
        },
        runs,
    );
    let bytes = proof.to_bytes();
    assert!(R1CSProof::<C>::from_bytes(&bytes).is_ok());
    let backend = if backend == Backend::Bp { "BP" } else { "BP++" };
    row(C::NAME, &format!("R1CS 2^{}", n.trailing_zeros()), backend, bytes.len(), prove, verify);
}

fn table<C: Curve>() {
    range::<C>(21);
    for b in [Backend::Bp, Backend::Bppp] {
        r1cs::<C>(1 << 10, b, 7);
        r1cs::<C>(1 << 14, b, 3);
    }
}

fn main() {
    println!("| curve | proof | backend | size | prove | verify |");
    println!("|---|---|---|---|---|---|");
    table::<Ristretto>();
    table::<Secp256k1>();
}

#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

use bulletproofs::bppp::{self, wnla, WnlaStatement};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use sha3::Sha3_512;

fn points(label: &str, n: usize) -> Vec<RistrettoPoint> {
    (0..n)
        .map(|i| RistrettoPoint::hash_from_bytes::<Sha3_512>(format!("{}{}", label, i).as_bytes()))
        .collect()
}

/// WNLA with |l| = 16 and |n| = 2^k: the shape inside an arithmetic circuit proof.
fn wnla_bench(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    for &k in &[10usize, 14] {
        let (a, b) = (16, 1usize << k);
        let (G, H, N) = (points("G", 1)[0], points("H", a), points("N", b));
        let cvec: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
        let st = WnlaStatement { g: &G, h_vec: &H, n_vec: &N, c: &cvec, rho: Scalar::random(&mut rng) };
        let l: Vec<Scalar> = (0..a).map(|_| Scalar::random(&mut rng)).collect();
        let n: Vec<Scalar> = (0..b).map(|_| Scalar::random(&mut rng)).collect();
        let C = st.commit(&l, &n);
        c.bench_function(&format!("wnla prove n=2^{}", k), |bench| {
            bench.iter(|| wnla::prove(&st, &C, &mut Transcript::new(b"bench"), l.clone(), n.clone()).unwrap())
        });
        let proof = wnla::prove(&st, &C, &mut Transcript::new(b"bench"), l.clone(), n.clone()).unwrap();
        c.bench_function(&format!("wnla verify n=2^{}", k), |bench| {
            bench.iter(|| proof.verify(&st, &C, &mut Transcript::new(b"bench")).unwrap())
        });
    }
}

/// `n` multiplications `w_L * w_R = w_O` and `n` random linear constraints with three terms
/// each over `w_L || w_R || w_O`: a circuit both backends express directly.
struct Gates {
    n: usize,
    w_l: Vec<Scalar>,
    w_r: Vec<Scalar>,
    w_o: Vec<Scalar>,
    rows: Vec<(Vec<(usize, Scalar)>, Scalar)>,
}

fn gates(n: usize) -> Gates {
    use rand_chacha::rand_core::{RngCore, SeedableRng};
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(n as u64);
    let w_l: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let w_r: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let w_o: Vec<Scalar> = w_l.iter().zip(&w_r).map(|(a, b)| a * b).collect();
    let full: Vec<Scalar> = w_l.iter().chain(&w_r).chain(&w_o).copied().collect();
    let rows = (0..n)
        .map(|_| {
            let terms: Vec<(usize, Scalar)> =
                (0..3).map(|_| (rng.next_u32() as usize % (3 * n), Scalar::random(&mut rng))).collect();
            let constant = -terms.iter().map(|(c, v)| v * full[*c]).sum::<Scalar>();
            (terms, constant)
        })
        .collect();
    Gates { n, w_l, w_r, w_o, rows }
}

fn bppp_circuit(g: &Gates) -> (bppp::ArithmeticCircuit, bppp::CircuitWitness) {
    let n = g.n;
    let mut w_l = bppp::SparseMatrix::new(3 * n);
    for (terms, _) in &g.rows {
        w_l.push_row(terms.iter().copied());
    }
    let mut w_m = bppp::SparseMatrix::new(3 * n);
    for r in 0..n {
        w_m.push_row(vec![(2 * n + r, Scalar::ONE)]);
    }
    let c = bppp::ArithmeticCircuit {
        n_m: n,
        n_o: n,
        n_v: 1,
        n_lin: 0,
        k: 0,
        w_l,
        a_l: g.rows.iter().map(|(_, k)| *k).collect(),
        w_m,
        a_m: vec![Scalar::ZERO; n],
        f_l: false,
        f_m: false,
        partition: (0..n).map(|r| (bppp::Slot::NormO, r)).collect(),
    };
    let w = bppp::CircuitWitness { w_l: g.w_l.clone(), w_r: g.w_r.clone(), w_o: g.w_o.clone(), v: vec![], s: vec![] };
    (c, w)
}

/// The same circuit as a BP++ arithmetic circuit and (with `yoloproofs`) as BP R1CS.
fn circuit_bench(c: &mut Criterion) {
    let pc = bulletproofs::PedersenGens::default();
    for &k in &[10usize, 14] {
        let g = gates(1 << k);
        let bp = bulletproofs::BulletproofGens::new(1 << k, 1);
        let (circ, w) = bppp_circuit(&g);
        let gens = bppp::BpppGens::new(&pc, &bp, 0, g.n).unwrap();
        let mut rng = rand::thread_rng();
        let proof = bppp::circuit::prove(&circ, &gens, &[], &w, &mut Transcript::new(b"bench"), &mut rng).unwrap();
        println!("BP++ circuit, {} multiplications: proof {} bytes", g.n, proof.to_bytes().len());
        c.bench_function(&format!("circuit n=2^{} BP++ prove", k), |b| {
            b.iter(|| bppp::circuit::prove(&circ, &gens, &[], &w, &mut Transcript::new(b"bench"), &mut rng).unwrap())
        });
        c.bench_function(&format!("circuit n=2^{} BP++ verify", k), |b| {
            b.iter(|| proof.verify(&circ, &gens, &[], &mut Transcript::new(b"bench")).unwrap())
        });
        #[cfg(feature = "yoloproofs")]
        r1cs_bench(c, k, &g, &pc, &bp);
    }
}

#[cfg(feature = "yoloproofs")]
fn r1cs_bench(
    c: &mut Criterion,
    k: usize,
    g: &Gates,
    pc: &bulletproofs::PedersenGens,
    bp: &bulletproofs::BulletproofGens,
) {
    use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, Variable, Verifier};
    fn constrain<CS: ConstraintSystem>(cs: &mut CS, g: &Gates, vars: &[Variable]) {
        for (terms, constant) in &g.rows {
            let lc: LinearCombination =
                terms.iter().map(|(col, v)| (vars[*col], *v)).chain(core::iter::once((Variable::One(), *constant))).collect();
            cs.constrain(lc);
        }
    }
    let prove = || {
        let mut t = Transcript::new(b"bench");
        let mut prover = Prover::new(pc, &mut t);
        let mut vars = vec![Variable::One(); 3 * g.n];
        for i in 0..g.n {
            let (l, r, o) = prover.allocate_multiplier(Some((g.w_l[i], g.w_r[i]))).unwrap();
            vars[i] = l;
            vars[g.n + i] = r;
            vars[2 * g.n + i] = o;
        }
        constrain(&mut prover, g, &vars);
        prover.prove(bp).unwrap()
    };
    let proof = prove();
    println!("BP R1CS, {} multiplications: proof {} bytes", g.n, proof.serialized_size());
    let prove_bppp = || {
        let mut t = Transcript::new(b"bench");
        let mut prover = Prover::new(pc, &mut t);
        prover.set_backend(bulletproofs::r1cs::Backend::Bppp);
        let mut vars = vec![Variable::One(); 3 * g.n];
        for i in 0..g.n {
            let (l, r, o) = prover.allocate_multiplier(Some((g.w_l[i], g.w_r[i]))).unwrap();
            vars[i] = l;
            vars[g.n + i] = r;
            vars[2 * g.n + i] = o;
        }
        constrain(&mut prover, g, &vars);
        prover.prove(bp).unwrap()
    };
    println!("BP++ via R1CS, {} multiplications: proof {} bytes", g.n, prove_bppp().serialized_size());
    c.bench_function(&format!("circuit n=2^{} BP++ via R1CS prove", k), |b| b.iter(prove_bppp));
    c.bench_function(&format!("circuit n=2^{} BP R1CS prove", k), |b| b.iter(prove));
    c.bench_function(&format!("circuit n=2^{} BP R1CS verify", k), |b| {
        b.iter(|| {
            let mut t = Transcript::new(b"bench");
            let mut verifier = Verifier::new(&mut t);
            let mut vars = vec![Variable::One(); 3 * g.n];
            for i in 0..g.n {
                let (l, r, o) = verifier.allocate_multiplier(None).unwrap();
                vars[i] = l;
                vars[g.n + i] = r;
                vars[2 * g.n + i] = o;
            }
            constrain(&mut verifier, g, &vars);
            verifier.verify(&proof, pc, bp).unwrap()
        })
    });
}

/// 64-bit range proof: the BP++ front end (base 16, inline multiplicities) against the BP
/// `RangeProof`.
fn range_bench(c: &mut Criterion) {
    let pc = bulletproofs::PedersenGens::default();
    let value = 0x0123_4567_89ab_cdefu64;
    let blinding = Scalar::from(12345u64);
    let st = bppp::RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
    let bp = bulletproofs::BulletproofGens::new(st.generators_capacity().max(64), 1);
    let mut rng = rand::thread_rng();
    let prove = |rng: &mut rand::rngs::ThreadRng| {
        bppp::RangeProof::prove(&st, &pc, &bp, &[value], &[blinding], &mut Transcript::new(b"bench"), rng).unwrap()
    };
    let (proof, V) = prove(&mut rng);
    println!("BP++ 64-bit range proof: {} bytes", proof.to_bytes().len());
    c.bench_function("range 64-bit BP++ prove", |b| b.iter(|| prove(&mut rng)));
    c.bench_function("range 64-bit BP++ verify", |b| {
        b.iter(|| proof.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"bench")).unwrap())
    });
    let (bp_proof, bp_V) =
        bulletproofs::RangeProof::prove_single(&bp, &pc, &mut Transcript::new(b"bench"), value, &blinding, 64).unwrap();
    println!("BP 64-bit range proof: {} bytes", bp_proof.to_bytes().len());
    c.bench_function("range 64-bit BP prove", |b| {
        b.iter(|| bulletproofs::RangeProof::prove_single(&bp, &pc, &mut Transcript::new(b"bench"), value, &blinding, 64).unwrap())
    });
    c.bench_function("range 64-bit BP verify", |b| {
        b.iter(|| bp_proof.verify_single(&bp, &pc, &mut Transcript::new(b"bench"), &bp_V, 64).unwrap())
    });

    // A multi-asset transaction: 2 inputs, 2 outputs, two asset types.
    let mst = bppp::MactStatement::new(16, 2, 2).unwrap();
    let mbp = bulletproofs::BulletproofGens::new(mst.generators_capacity(), 1);
    let e = |amount: u64, asset: u64, s: u64| bppp::MactEntry { amount, asset: Scalar::from(asset), blinding: Scalar::from(s) };
    let (ins, outs) = ([e(100, 1, 1), e(50, 2, 2)], [e(100, 1, 3), e(50, 2, 4)]);
    let mprove = |rng: &mut rand::rngs::ThreadRng| {
        bppp::MactProof::prove(&mst, &pc, &mbp, &ins, &outs, &mut Transcript::new(b"bench"), rng).unwrap()
    };
    let (mproof, mV) = mprove(&mut rng);
    println!("BP++ MACT 2 in / 2 out: {} bytes", mproof.to_bytes().len());
    c.bench_function("mact 2x2 BP++ prove", |b| b.iter(|| mprove(&mut rng)));
    c.bench_function("mact 2x2 BP++ verify", |b| {
        b.iter(|| mproof.verify(&mst, &pc, &mbp, &mV, &mut Transcript::new(b"bench")).unwrap())
    });
}

criterion_group! {
    name = bppp;
    config = Criterion::default().sample_size(10);
    targets = wnla_bench, circuit_bench, range_bench,
}

criterion_main!(bppp);

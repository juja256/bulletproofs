//! Time, proof size and peak memory of one BP++ / BP proof, one configuration per process
//! (so that the peak RSS is that of this configuration):
//!
//! ```sh
//! cargo run --release --example bppp_profile -- circuit 14
//! cargo run --release --example bppp_profile -- wnla 14
//! cargo run --release --example bppp_profile -- r1cs 14 bppp
//! cargo run --release --example bppp_profile -- builder 1024 bp
//! ```

#![allow(non_snake_case)]

use std::time::Instant;

use bulletproofs::bppp::{self, ArithmeticCircuit, BpppGens, CircuitWitness, Slot, SparseMatrix, WnlaStatement};
use bulletproofs::r1cs::{Backend, ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use bulletproofs::curve::Ristretto;

fn peak_rss_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|kb| kb.parse::<f64>().ok())
        .map_or(0.0, |kb| kb / 1024.0)
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

/// `n` multiplications and `n` random linear rows of three terms (as the benchmark).
struct Gates {
    n: usize,
    w_l: Vec<Scalar>,
    w_r: Vec<Scalar>,
    rows: Vec<(Vec<(usize, Scalar)>, Scalar)>,
}

fn gates(n: usize) -> Gates {
    let mut r = ChaCha20Rng::seed_from_u64(n as u64);
    let w_l: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut r)).collect();
    let w_r: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut r)).collect();
    let w: Vec<Scalar> = w_l.iter().chain(&w_r).copied().chain(w_l.iter().zip(&w_r).map(|(a, b)| a * b)).collect();
    let rows = (0..n)
        .map(|i| {
            let terms: Vec<(usize, Scalar)> =
                [i, n + (i * 7 + 1) % n, 2 * n + (i * 13 + 5) % n].iter().map(|c| (*c, Scalar::random(&mut r))).collect();
            let a = -terms.iter().map(|(c, v)| v * w[*c]).sum::<Scalar>();
            (terms, a)
        })
        .collect();
    Gates { n, w_l, w_r, rows }
}

fn circuit(g: &Gates) -> (ArithmeticCircuit<Scalar>, CircuitWitness<Scalar>) {
    let n = g.n;
    let mut w_l = SparseMatrix::new(3 * n);
    for (terms, _) in &g.rows {
        w_l.push_row(terms.iter().copied());
    }
    let mut w_m = SparseMatrix::new(3 * n);
    for i in 0..n {
        w_m.push_row(vec![(2 * n + i, Scalar::ONE)]);
    }
    let c = ArithmeticCircuit {
        n_m: n,
        n_o: n,
        n_v: 1,
        n_lin: 0,
        k: 0,
        w_l,
        a_l: g.rows.iter().map(|(_, a)| *a).collect(),
        w_m,
        a_m: vec![Scalar::ZERO; n],
        f_l: false,
        f_m: false,
        partition: (0..n).map(|i| (Slot::NormO, i)).collect(),
    };
    let w_o = g.w_l.iter().zip(&g.w_r).map(|(a, b)| a * b).collect();
    (c, CircuitWitness { w_l: g.w_l.clone(), w_r: g.w_r.clone(), w_o, v: vec![], s: vec![] })
}

fn r1cs<CS: ConstraintSystem<Scalar>>(cs: &mut CS, g: &Gates, prover: bool) {
    let mut vars = vec![Variable::ONE; 3 * g.n];
    for i in 0..g.n {
        let ab = if prover { Some((g.w_l[i], g.w_r[i])) } else { None };
        let (l, r) = (cs.witness(ab.map(|p| p.0)).unwrap(), cs.witness(ab.map(|p| p.1)).unwrap());
        let o = cs.multiply(l.into(), r.into()).unwrap();
        vars[i] = l;
        vars[g.n + i] = r;
        vars[2 * g.n + i] = o;
    }
    for (terms, constant) in &g.rows {
        let lc: LinearCombination<Scalar> = terms.iter().map(|(c, v)| (vars[*c], *v)).chain(Some((Variable::ONE, *constant))).collect();
        cs.constrain(lc);
    }
}

fn range32<CS: ConstraintSystem<Scalar>>(cs: &mut CS, vars: &[Variable], vals: Option<&[u64]>) -> Result<(), R1CSError> {
    let byte = cs.table((0..256u64).map(|x| vec![x]).collect())?;
    for (i, x) in vars.iter().enumerate() {
        let mut sum = LinearCombination::default();
        for j in 0..4 {
            let b = cs.lookup_value(byte, vals.map(|v| (v[i] >> (8 * j)) & 255))?;
            sum = sum + b * Scalar::from(1u64 << (8 * j));
        }
        cs.constrain(*x - sum);
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.get(0).map(String::as_str).unwrap_or("circuit");
    let size: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let backend = match args.get(2).map(String::as_str) {
        Some("bp") => Backend::Bp,
        _ => Backend::Bppp,
    };
    let pc = PedersenGens::<Ristretto>::default();
    let mut rng = ChaCha20Rng::seed_from_u64(7);
    let (prove_ms, verify_ms, bytes, label) = match mode {
        "wnla" => {
            let n = 1usize << size;
            let bp = BulletproofGens::new(n.max(7), 1);
            let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
            let (h_vec, n_vec, g) = (gens.h.clone(), gens.n.to_vec(), gens.g);
            let c: Vec<Scalar> = (0..7).map(|_| Scalar::random(&mut rng)).collect();
            let st = WnlaStatement::<bulletproofs::curve::Ristretto> { g: &g, h: &h_vec, n: &n_vec, c: &c, rho: Scalar::from(3u64) };
            let l: Vec<Scalar> = (0..7).map(|_| Scalar::random(&mut rng)).collect();
            let nv: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let C: RistrettoPoint = st.commit(&l, &nv);
            let t = Instant::now();
            let p = bppp::WnlaProof::prove(&st, &C, &mut Transcript::new(b"p"), l, nv).unwrap();
            let pm = ms(t);
            let t = Instant::now();
            p.verify(&st, &C, &mut Transcript::new(b"p")).unwrap();
            (pm, ms(t), p.to_bytes().len(), format!("wnla |n|=2^{}", size))
        }
        "circuit" => {
            let g = gates(1 << size);
            let (c, w) = circuit(&g);
            let bp = BulletproofGens::new(g.n.max(6), 1);
            let gens = BpppGens::new(&pc, &bp, 0, g.n).unwrap();
            let t = Instant::now();
            let p = bppp::CircuitProof::prove(&c, &gens, &[], &w, &mut Transcript::new(b"p"), &mut rng).unwrap();
            let pm = ms(t);
            let t = Instant::now();
            p.verify(&c, &gens, &[], &mut Transcript::new(b"p")).unwrap();
            (pm, ms(t), p.to_bytes().len(), format!("circuit n=2^{}", size))
        }
        "r1cs" => {
            let g = gates(1 << size);
            let bp = BulletproofGens::new(g.n.max(6), 1);
            let t = Instant::now();
            let mut tr = Transcript::new(b"p");
            let mut p = Prover::new(&pc, &mut tr);
            p.set_backend(backend);
            r1cs(&mut p, &g, true);
            let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
            let pm = ms(t);
            let t = Instant::now();
            let mut tr = Transcript::new(b"p");
            let mut v = Verifier::new(&mut tr);
            v.set_backend(backend);
            r1cs(&mut v, &g, false);
            v.verify(&proof, &pc, &bp).unwrap();
            (pm, ms(t), proof.to_bytes().len(), format!("r1cs {:?} n=2^{}", backend, size))
        }
        "builder" => {
            let vals: Vec<u64> = (0..size as u64).map(|i| i.wrapping_mul(0x9e37_79b9) & 0xffff_ffff).collect();
            let run_p = || {
                let mut p = Prover::new(&pc, Transcript::new(b"p"));
                p.set_backend(backend);
                let (V, vars): (Vec<_>, Vec<_>) = vals.iter().map(|v| p.commit(Scalar::from(*v), Scalar::from(7u64))).unzip();
                range32(&mut p, &vars, Some(&vals)).unwrap();
                let cap = p.cost().gens_capacity(backend);
                (p, V, cap)
            };
            let bp = BulletproofGens::new(run_p().2, 1);
            let t = Instant::now();
            let (p, V, _) = run_p();
            let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
            let pm = ms(t);
            let t = Instant::now();
            let mut tr = Transcript::new(b"p");
            let mut v = Verifier::new(&mut tr);
            v.set_backend(backend);
            let vars: Vec<Variable> = V.iter().map(|x| v.commit(*x)).collect();
            range32(&mut v, &vars, None).unwrap();
            v.verify(&proof, &pc, &bp).unwrap();
            (pm, ms(t), proof.to_bytes().len(), format!("builder {:?} {} x range32", backend, size))
        }
        "batch" => {
            let st = bppp::RangeStatement::new(16, vec![(0, 1 << 64)]).unwrap();
            let bp = BulletproofGens::new(st.generators_capacity(), 1);
            let proofs: Vec<_> = (0..size as u64)
                .map(|i| bppp::RangeProof::prove(&st, &pc, &bp, &[i * 0x9e37_79b9], &[Scalar::from(i)], &mut Transcript::new(b"p"), &mut rng).unwrap())
                .collect();
            let t = Instant::now();
            for (p, V) in &proofs {
                p.verify(&st, &pc, &bp, V, &mut Transcript::new(b"p")).unwrap();
            }
            let single = ms(t);
            let t = Instant::now();
            let mut b = bppp::BatchVerifier::new(&pc, &bp, ChaCha20Rng::seed_from_u64(1));
            for (p, V) in &proofs {
                b.add_range(p, &st, V, &mut Transcript::new(b"p")).unwrap();
            }
            b.verify().unwrap();
            println!("{} x 64-bit range proofs: one by one {:.1} ms, batch {:.1} ms", size, single, ms(t));
            return;
        }
        "micro" => {
            use curve25519_dalek::traits::{MultiscalarMul, VartimeMultiscalarMul};
            let n = 1usize << size;
            let bp = BulletproofGens::new(n, 1);
            let gens = BpppGens::new(&pc, &bp, 0, n).unwrap();
            let pts = gens.n.to_vec();
            let sc: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let t = Instant::now();
            let _ = RistrettoPoint::multiscalar_mul(&sc, &pts);
            let ct = ms(t) * 1e3 / n as f64;
            let t = Instant::now();
            let _ = RistrettoPoint::vartime_multiscalar_mul(&sc, &pts);
            let vt = ms(t) * 1e3 / n as f64;
            let t = Instant::now();
            for i in 0..n / 2 {
                let _ = RistrettoPoint::vartime_multiscalar_mul([sc[2 * i], sc[2 * i + 1]], [pts[2 * i], pts[2 * i + 1]]);
            }
            let fold = ms(t) * 1e3 / (n / 2) as f64;
            let t = Instant::now();
            for i in 0..n / 2 {
                let _ = pts[2 * i] + RistrettoPoint::vartime_multiscalar_mul([sc[2 * i + 1]], [pts[2 * i + 1]]);
            }
            let fold1 = ms(t) * 1e3 / (n / 2) as f64;
            let t = Instant::now();
            for i in 0..n / 2 {
                let _ = pts[2 * i] + pts[2 * i + 1] * sc[2 * i + 1];
            }
            let fold1ct = ms(t) * 1e3 / (n / 2) as f64;
            println!("P + s Q: VT {:.2} us, CT {:.2} us", fold1, fold1ct);
            let t = Instant::now();
            let mut acc = pts[0];
            for p in &pts[1..] {
                acc += p;
            }
            let add = ms(t) * 1e3 / n as f64;
            println!("n=2^{}: CT MSM {:.2} us/term, VT MSM {:.2} us/term, 2-point fold {:.2} us, add {:.3} us", size, ct, vt, fold, add);
            return;
        }
        m => panic!("unknown mode {}", m),
    };
    println!("{:<34} prove {:>10.1} ms  verify {:>9.1} ms  proof {:>6} B  peak RSS {:>8.1} MB", label, prove_ms, verify_ms, bytes, peak_rss_mb());
}

//! Costs of the Simplicity verifier of R1CS circuits (BP++ backend, secp256k1, SHA-256
//! transcript): chains of multiplications of growing size, compiled, proven and run as a node
//! would run them.
//!
//! cargo run --release --example simplicity_costs --features simplicity [max log2 gates]

use std::time::Instant;

use bulletproofs::curve::Secp256k1;
use bulletproofs::r1cs::{lc, Backend, ConstraintSystem, Prover, Variable, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use k256::Scalar;
use bulletproofs::simplicity::{dummy_env, sighash_of, CompileTranscript, SIGHASH_LABEL};
use bulletproofs::{Sha256Transcript, TranscriptBackend};
use rand_chacha::rand_core::SeedableRng;

/// `n` multiplications `v_{i+1} = v_i · x` from a committed `x`, and the last value fixed.
fn chain<CS: ConstraintSystem<Scalar>>(cs: &mut CS, x: Variable, n: usize, last: Scalar) {
    let mut v = lc(x);
    for _ in 0..n {
        let o = cs.multiply(v, lc(x)).unwrap();
        v = lc(o);
    }
    cs.constrain(v - last);
}

fn main() {
    let max: u32 = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(10);
    let env = dummy_env();
    let x = Scalar::from(3u64);
    println!("| gates | tape ops | MSM terms | steps | stored | cost (mWU) | budget (mWU) | jets | data | program B | B/gate | witness B | cells | tx WU | compile | run |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
    for lg in 1..=max {
        let n = 1usize << lg;
        let pc = PedersenGens::<Secp256k1>::default();
        let bp = BulletproofGens::<Secp256k1>::new(2 * n + 64, 1);
        let mut last = x;
        for _ in 0..n {
            last *= x;
        }
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(lg as u64);
        let mut t = Sha256Transcript::new(b"chain");
        t.append_message(SIGHASH_LABEL, &sighash_of(&env));
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(Backend::Bppp);
        let (cx, xv) = p.commit(x, <Scalar as bulletproofs::curve::ff::Field>::random(&mut rng));
        chain(&mut p, xv, n, last);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();

        let t0 = Instant::now();
        let mut ct = CompileTranscript::new(b"chain");
        ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
        let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
        v.set_backend(Backend::Bppp);
        let xv = v.commit(cx);
        chain(&mut v, xv, n, last);
        let sv = v.compile_to_simplicity(&pc, &bp).unwrap();
        let compile = t0.elapsed();
        let st = sv.stats().clone();
        let jets = jet_cost(&st.jets);
        let t1 = Instant::now();
        let w = sv.witness(&proof).unwrap();
        match sv.execute(&w, &env) {
            Ok(r) => {
                // the input's weight: its witness stack (program, witness, CMR, control block),
                // or more if the cost needs padding
                let stack = (r.budget_mwu / 1000 - 50) as usize;
                let tx = stack.max((r.cost_mwu / 1000) as usize);
                println!(
                    "| {} | {} | {} | {} | {} | {} | {} | {:.0}% | {:.0}% | {} | {} | {} | {} | {} | {:.1?} | {:.1?} |",
                    n, st.tape_ops, st.msm_terms, st.steps, st.stored, r.cost_mwu, r.budget_mwu, 100.0 * jets as f64 / r.cost_mwu as f64, 100.0 * r.data_mwu as f64 / r.cost_mwu as f64,
                    r.program_bytes, r.program_bytes / n, r.witness_bytes, r.cells, tx, compile, t1.elapsed()
                )
            }
            Err(e) => println!("| {} | {} | {} | {} | {} | {:?} | | | | | | | | | {:.1?} | {:.1?} |", n, st.tape_ops, st.msm_terms, st.steps, st.stored, e, compile, t1.elapsed()),
        }
    }
}

/// The jets' fixed costs (simplicity-lang 0.9, mWU), summed over the program.
fn jet_cost(jets: &std::collections::BTreeMap<&'static str, usize>) -> u64 {
    let price = |j: &str| -> u64 {
        match j {
            "scale" => 72675,
            "decompress" => 10861,
            "gej_add" => 2897,
            "gej_is_infinity" => 666,
            "scalar_add" => 739,
            "scalar_multiply" => 774,
            "scalar_negate" => 490,
            "scalar_invert" => 3193,
            "scalar_normalize" => 472,
            "scalar_is_zero" => 271,
            "eq_256" => 225,
            "sha_256_ctx_8_add_64" => 1187,
            "sha_256_ctx_8_add_32" => 896,
            "sha_256_ctx_8_finalize" => 835,
            "sig_all_hash" => 133,
            _ => 700,
        }
    };
    jets.iter().map(|(j, n)| price(j) * *n as u64).sum()
}

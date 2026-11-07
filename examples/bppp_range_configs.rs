//! Size, first and median prove / verify time of BP++ range proofs for `bits`-bit values in
//! batches of `count` (the configurations fastcrypto's README reports); the first proof of a
//! shape also builds the cached generator tables. Serial unless built with `parallel`:
//!
//! ```sh
//! cargo run --release --example bppp_range_configs                      # ristretto255, base 16, 50 runs
//! cargo run --release --example bppp_range_configs -- 256 20 secp256k1  # base 256, 20 runs
//! ```

#![allow(non_snake_case)]

use std::time::Instant;

use bulletproofs::bppp::{RangeProof, RangeStatement};
use bulletproofs::curve::ff::Field;
use bulletproofs::curve::{Curve, Ristretto, Secp256k1};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use rand_chacha::rand_core::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

const CONFIGS: [(u32, usize); 8] = [(16, 1), (32, 1), (64, 1), (16, 4), (16, 8), (32, 8), (64, 16), (64, 32)];

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let base: u64 = args.get(1).map_or(16, |a| a.parse().expect("base"));
    let runs: usize = args.get(2).map_or(50, |a| a.parse().expect("runs"));
    match args.get(3).map_or("ristretto255", |a| a.as_str()) {
        "secp256k1" => run::<Secp256k1>(base, runs),
        _ => run::<Ristretto>(base, runs),
    }
}

fn run<C: Curve>(base: u64, runs: usize) {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let pc = PedersenGens::<C>::default();
    println!("{}, base {}, median of {} runs", C::NAME, base, runs);
    println!("{:>6} {:>6} {:>10} {:>10} {:>10} {:>10}", "config", "bytes", "1st prove", "1st verify", "prove ms", "verify ms");
    for (bits, count) in CONFIGS {
        let bound = 1u128 << bits;
        let st = RangeStatement::new(base, vec![(0, bound); count]).unwrap();
        let bp = BulletproofGens::<C>::new(st.generators_capacity(), 1);
        let values: Vec<u64> = (0..count).map(|_| (rng.next_u64() as u128 % bound) as u64).collect();
        let blindings: Vec<C::Scalar> = (0..count).map(|_| C::Scalar::random(&mut rng)).collect();
        let (mut prove, mut verify) = (Vec::new(), Vec::new());
        let mut bytes = 0;
        for _ in 0..runs {
            let t = Instant::now();
            let (proof, V) = RangeProof::<C>::prove(&st, &pc, &bp, &values, &blindings, &mut Transcript::new(b"cfg"), &mut rng).unwrap();
            prove.push(t.elapsed().as_secs_f64() * 1e3);
            bytes = proof.to_bytes().len();
            let t = Instant::now();
            proof.verify(&st, &pc, &bp, &V, &mut Transcript::new(b"cfg")).unwrap();
            verify.push(t.elapsed().as_secs_f64() * 1e3);
        }
        let (p1, v1) = (prove[0], verify[0]);
        println!("{:>6} {:>6} {:>10.2} {:>10.2} {:>10.2} {:>10.2}", format!("{}x{}", bits, count), bytes, p1, v1, median(prove), median(verify));
    }
}

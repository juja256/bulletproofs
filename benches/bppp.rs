#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

use bulletproofs::bppp::{wnla, WnlaStatement};
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

criterion_group! {
    name = bppp;
    config = Criterion::default().sample_size(10);
    targets = wnla_bench,
}

criterion_main!(bppp);

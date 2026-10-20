//! Multiscalar multiplication on each curve: constant time (secret scalars, the prover's
//! commitments) and variable time (public scalars, verification), 2^10, 2^14 and 2^17 terms.
//! Per-term times are the reported time divided by the size.

#[macro_use]
extern crate criterion;
use criterion::{BenchmarkId, Criterion, Throughput};

use bulletproofs::curve::ff::Field;
use bulletproofs::curve::group::Group;
use bulletproofs::curve::{Curve, Ristretto};
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

fn msm<C: Curve>(c: &mut Criterion) {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let max = 1 << 17;
    let s: Vec<C::Scalar> = (0..max).map(|_| C::Scalar::random(&mut rng)).collect();
    let p: Vec<C::Point> = (0..max).map(|_| C::Point::random(&mut rng)).collect();
    let mut group = c.benchmark_group(format!("msm {}", C::NAME));
    group.sample_size(10);
    for &n in &[1usize << 10, 1 << 14, 1 << 17] {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("ct", n), &n, |b, &n| b.iter(|| C::msm_ct(&s[..n], &p[..n])));
        group.bench_with_input(BenchmarkId::new("vt", n), &n, |b, &n| b.iter(|| C::msm_vt(&s[..n], &p[..n])));
    }
    group.finish();
}

#[cfg(feature = "secp256k1")]
criterion_group!(curves, msm::<Ristretto>, msm::<bulletproofs::curve::Secp256k1>);
#[cfg(not(feature = "secp256k1"))]
criterion_group!(curves, msm::<Ristretto>);
criterion_main!(curves);

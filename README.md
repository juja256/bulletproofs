# Bulletproofs

<img
 width="100%"
 src="https://doc.dalek.rs/assets/bulletproofs-rangeproof.png"
/>

The fastest [Bulletproofs][bp_website] implementation ever, featuring
single and aggregated range proofs, strongly-typed multiparty
computation, and a programmable constraint system API for proving
arbitrary statements (under development).

This library implements Bulletproofs using [Ristretto][ristretto],
using the `ristretto255` implementation in
[`curve25519-dalek`][curve25519_dalek].  When using the [parallel
formulas][parallel_edwards] in the `curve25519-dalek` AVX2 backend, it
can verify 64-bit rangeproofs **approximately twice as fast** as the
original `libsecp256k1`-based Bulletproofs implementation.

This library provides implementations of:

* Single-party proofs of single or multiple ranges, using the
  aggregated rangeproof construction;

* Online multi-party computation for rangeproof aggregation between
  multiple parties, using [session types][session_type_blog] to
  statically enforce correct protocol flow;
  
* A programmable constraint system API for expressing rank-1
  constraint systems, and proving and verifying proofs of arbitrary
  statements (unstable, under development with the `yoloproofs` feature);
  
* Online multi-party computation for aggregated constraint system proofs
  (planned future work).

These proofs are implemented using [Merlin transcripts][doc_merlin],
allowing them to be arbitrarily composed with other proofs without
implementation changes.

The development roadmap can be found in the
[Milestones][gh_milestones] section of the [Github repo][gh_repo].

The constraint system API is provided **FOR EXPERIMENTS ONLY**, and must be
enabled by specifying the `yoloproofs` feature.  It is not covered by semver
compatibility and is **SUBJECT TO CHANGE WITHOUT NOTICE**.  

Currently, the `yoloproofs` feature is disabled in the published version of the
crate, so it can only be used by specifying a git dependency on the `develop`
branch.  This means that it is not possible to publish a crate using the R1CS
API, because it is **FOR EXPERIMENTS ONLY**.

## Documentation
  
The user-facing documentation for this functionality can be [found
here][doc_external].  In addition, the library *also* contains
extensive notes on how Bulletproofs work.  These notes can be found in
the library's [internal documentation][doc_internal]:

* how [Bulletproofs work][bp_notes];
* how [the range proof protocol works][rp_notes];
* how [the inner product proof protocol works][ipp_notes];
* how [the aggregation protocol works][agg_notes];
* how the Bulletproof constraint system proofs work (under development);
* how the constraint system reduction works (under development);
* how the aggregated constraint system proofs work (future work).

## Comparative Performance

The following table gives comparative timings for proving and verification of a
64-bit rangeproof on an Intel Skylake-X i7-7800X (@3.5GHz, Turbo Boost
disabled).  Times are in microseconds (lower is better), with the relative
speed compared to the fastest implementation.

| Implementation | Group            | Proving (μs) |       rel | Verification (μs) |       rel |
|----------------|------------------|-------------:|----------:|------------------:|----------:|
| ours (avx2)    | ristretto255     |         7300 | **1.00x** |              1040 | **1.00x** |
| ours (u64)     | ristretto255     |        11300 | **1.54x** |              1490 | **1.43x** |
| libsecp+endo   | secp256k1        |        14300 | **1.96x** |              1900 | **1.83x** |
| libsecp-endo   | secp256k1        |        16800 | **2.30x** |              2080 | **2.00x** |
| Monero         | ed25519 (unsafe) |        53300 | **7.30x** |              4810 | **4.63x** |

Use of the `curve25519-dalek` IFMA backend gives another 1.5x speedup on a
Cannonlake i3-8121U, increasing the verification speedup **3x** over libsecp
and **7x** over Monero, but these processors are not yet generally available.

This crate also contains other benchmarks; see the *Tests and Benchmarks*
section below for details on how to run them all.

## Example

The following example shows how to create and verify a 32-bit rangeproof.

```rust
# // The #-commented lines are hidden in Rustdoc but not in raw
# // markdown rendering, and contain boilerplate code so that the
# // code in the README.md is actually run as part of the test suite.
#
# extern crate rand;
# use rand::thread_rng;
#
# extern crate curve25519_dalek;
# use curve25519_dalek::scalar::Scalar;
#
# extern crate merlin;
# use merlin::Transcript;
#
# extern crate bulletproofs;
# use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
#
# fn main() {
// Generators for Pedersen commitments.  These can be selected
// independently of the Bulletproofs generators.
let pc_gens = PedersenGens::default();

// Generators for Bulletproofs, valid for proofs up to bitsize 64
// and aggregation size up to 1.
let bp_gens = BulletproofGens::new(64, 1);

// A secret value we want to prove lies in the range [0, 2^32)
let secret_value = 1037578891u64;

// The API takes a blinding factor for the commitment.
let blinding = Scalar::random(&mut thread_rng());

// The proof can be chained to an existing transcript.
// Here we create a transcript with a doctest domain separator.
let mut prover_transcript = Transcript::new(b"doctest example");

// Create a 32-bit rangeproof.
let (proof, committed_value) = RangeProof::prove_single(
    &bp_gens,
    &pc_gens,
    &mut prover_transcript,
    secret_value,
    &blinding,
    32,
).expect("A real program could handle errors");

// Verification requires a transcript with identical initial state:
let mut verifier_transcript = Transcript::new(b"doctest example");
assert!(
    proof
        .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
        .is_ok()
);
# }
```
## Building

To compile successfully, you will need to have nightly Rust installed, rather than stable.

You can install nightly Rust with rustup:

```text
rustup default nightly
```

## Tests and Benchmarks

Run tests with `cargo test`.  Run benchmarks with `cargo bench`.  This crate
uses [criterion.rs][criterion] for benchmarks. 

## Features

The `yoloproofs` feature enables support for rank-1 constraint system proofs.
It is **UNSTABLE AND UNSUITABLE FOR DEPLOYMENT**, and **PROVIDED FOR TESTING
ONLY**.

The `parallel` feature (this fork) runs the prover and verifier on all threads with
[rayon](https://crates.io/crates/rayon): chunked multiscalar multiplications, the
polynomial passes and constraint flattening, the inner-product argument and generator
derivation. Proofs are identical to the serial ones.

### Prover and verifier optimisations in this fork

Compared to upstream, the R1CS prover needs about 3x less memory and is faster, the
verifier too, with byte-identical proofs (`tests/golden.rs` pins proof bytes produced by
upstream `d27dde0` with fixed randomness via `Prover::prove_with_rng`):

- multiscalar multiplications run in chunks over slices (no lookup tables or buffers
  for all points at once, no copies of the generators);
- constraints are stored compactly, 8 bytes per term (`r1cs::compact`), on both sides;
- the vector polynomials `l(X)`, `r(X)` are never materialised: `t(X)` is accumulated per
  index and `l(x)`, `r(x)` overwrite the witness vectors in place;
- the inner-product prover computes the first rounds from the input generators and
  materialises the folded generators once, instead of folding them every round.

The `avx2_backend` feature enables `curve25519-dalek`'s AVX2 backend,
which implements curve arithmetic using [parallel
formulas][parallel_edwards].  To use it for Bulletproofs, the
`target_cpu` must support AVX2:

```text
RUSTFLAGS="-C target_cpu=skylake" cargo bench --features "avx2_backend"
```

Skylake-X CPUs have double the AVX2 registers. To use them, try

```text
RUSTFLAGS="-C target_cpu=skylake-avx512" cargo bench --features "avx2_backend"
```

This prevents spills in the AVX2 parallel field multiplication code, but causes
worse code generation elsewhere ¯\\\_(ツ)\_/¯

## Bulletproofs++ (experimental)

The `bppp` feature adds Bulletproofs++ (Eagen, Kanjalkar, Ruffing, Nick, ePrint 2022/510) on
ristretto255. **Not audited; the API and the proof format will change.** The protocol as
implemented is pinned in [`docs/bppp/spec.md`](docs/bppp/spec.md). `ref/bppp_ref.py` is a
spec-level Python reference (symbolic group elements, a naive recursive verifier) that
generates the test vectors in `tests/vectors/bppp/`. Its norm-argument part has the same author
as the Rust code; its arithmetic-circuit part was written independently from the spec and the
paper. The norm argument in the reference also reproduces secp256k1-zkp's norm-argument test vectors byte for byte
(`python3 ref/xcheck_secp256k1_zkp.py`), which pins its algebra to the authors' implementation.

Status:

- `bppp::wnla`, the weighted norm linear argument. It binds its statement (`G`, `C`, `rho`, `c`) but
  is not zero-knowledge: a building block, not a proof system to use on its own.
- `bppp::circuit`, arithmetic circuits (paper §5, spec §3): `w_L ∘ w_R = W_m w + f_m w_V + a_m`,
  `W_l w + f_l w_V + a_l = 0` with sparse matrices, a partition of `w_O` and committed input
  vectors (`BpppGens::commit_input`; a single value is an ordinary `PedersenGens` commitment).
  The generators come from the same `PedersenGens` and `BulletproofGens` as the BP backend.
  The transcript binds the dimensions, the generators `G` and `H_0`, a SHA3 digest of the
  circuit and the inputs. The Rust prover reproduces the independently written circuit part of
  the Python reference (`tests/vectors/bppp/circuit.json`) commitment for commitment.

- `bppp::reciprocal`, reciprocal form circuits (paper §6.2–6.3, spec §4): private poles
  committed with the initial witness, reciprocals committed after the challenge `alpha`, and
  reciprocal rows (sums of reciprocals and public poles) that must vanish as rational functions.
  Numerators and multiplicities may only read columns committed before `alpha`. A reciprocal
  range proof (paper §6.4) is a small instance of it.

- `bppp::RangeProof`, range proofs for several values with arbitrary ranges `[A, B)`, `B - A`
  up to `2^64`, in any base `2..=256` (paper §6.4, spec §5.1–5.2). The digit layout is greedy and
  exact for every range (the paper's case analysis misses ranges smaller than the base); digits
  are computed in constant time.
- `bppp::MactProof`, multi-asset transactions (paper §6.5, spec §5.3): per asset type the
  inputs and outputs balance, and every output is in `[0, 2^64)`. Asset types are scalars
  committed with the amount (`amount B + blinding B_blinding + asset H_7`). **Input amounts
  are not range-checked**: as in the paper, the input commitments must already be known to
  open to amounts in `[0, 2^64)` (e.g. outputs of earlier verified proofs).

When multiplicities do not fit in the norm part (few digits, large base) they are shared in
the linear part, and the proof still carries an empty `C_O` (32 B) that the paper drops; for
example a 64-bit proof in base 256 is 704 B.

- The R1CS front end on BP++ (spec §6): `prover.set_backend(Backend::Bppp)` and
  `verifier.set_backend(Backend::Bppp)`; `prove`/`verify` and gadgets are unchanged. The
  constraint system is translated into an arithmetic circuit; randomized constraints are not
  supported on BP++ (they return a `GadgetError`).

`cargo bench --features bppp --bench bppp -- "range|mact"`:

| | proof | prove | verify |
|---|---|---|---|
| 64-bit range proof, BP++ (base 16) | 416 B | 2.55 ms | 0.48 ms |
| 64-bit range proof, BP `RangeProof` | 672 B | 4.39 ms | 0.61 ms |
| BP++ transaction, 2 inputs, 2 outputs, 2 asset types | 512 B | 4.76 ms | 0.64 ms |

The inaccuracies found in the paper are collected in
[`docs/bppp/bppp-paper-errors.tex`](docs/bppp/bppp-paper-errors.tex).

```sh
cargo test --release --features bppp --lib bppp
python3 ref/gen_vectors.py            # regenerate the vectors (deterministic)
cargo bench --features bppp --bench bppp
```

| WNLA, $\lvert l\rvert = 16$ | prove | verify |
|---|---|---|
| $\lvert n\rvert = 2^{10}$ | 38 ms | 2.6 ms |
| $\lvert n\rvert = 2^{14}$ | 591 ms | 30.5 ms |

The same circuit in both backends: $n$ multiplications $w_L w_R = w_O$ and $n$ random linear
constraints with three terms each (`cargo bench --features "bppp yoloproofs" --bench bppp -- circuit`):

| $n$ | proof BP++ / BP | prove BP++ / BP | verify BP++ / BP |
|---|---|---|---|
| $2^{10}$ | 800 / 1057 B | 69 / 66 ms | 3.9 / 5.9 ms |
| $2^{14}$ | 1056 / 1313 B | 1.10 / 0.99 s | 52 / 77 ms |

The BP++ prover is not optimised yet (phase 7 of the plan); verification is about a third
faster and proofs about a fifth smaller.

Apple M4 Pro, single-threaded, `rustc 1.99.1`, release profile.

## About

This is a research project sponsored by [Interstellar][interstellar],
developed by Henry de Valence, Cathie Yun, and Oleg Andreev.

[bp_website]: https://crypto.stanford.edu/bulletproofs/
[ristretto]: https://ristretto.group
[doc_merlin]: https://doc.dalek.rs/merlin/index.html
[doc_external]: https://doc.dalek.rs/bulletproofs/index.html
[doc_internal]: https://doc-internal.dalek.rs/bulletproofs/index.html
[bp_notes]: https://doc-internal.dalek.rs/bulletproofs/notes/index.html
[rp_notes]: https://doc-internal.dalek.rs/bulletproofs/range_proof/index.html
[ipp_notes]: https://doc-internal.dalek.rs/bulletproofs/inner_product_proof/index.html
[agg_notes]: https://doc-internal.dalek.rs/bulletproofs/notes/index.html#aggregated-range-proof
[criterion]: https://github.com/japaric/criterion.rs
[session_type_blog]: https://blog.chain.com/bulletproof-multi-party-computation-in-rust-with-session-types-b3da6e928d5d
[curve25519_dalek]: https://doc.dalek.rs/curve25519_dalek/index.html
[parallel_edwards]: https://medium.com/@hdevalence/accelerating-edwards-curve-arithmetic-with-parallel-formulas-ac12cf5015be
[gh_repo]: https://github.com/dalek-cryptography/bulletproofs/
[gh_milestones]: https://github.com/dalek-cryptography/bulletproofs/milestones
[interstellar]: https://interstellar.com/

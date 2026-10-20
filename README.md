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

The `bppp` feature (this fork) adds Bulletproofs++: its protocols in `bulletproofs::bppp` and a
second backend of the R1CS front end and the circuit builder (see
[Bulletproofs++](#bulletproofs-experimental) and
[Writing gadgets for both backends](#writing-gadgets-for-both-backends)).
`bppp-vartime` computes the BP++ norm argument in variable time (its inputs are uniformly
random given the transcript; same proofs, faster proving; constant time is the default).
`cheats` is for tests only: `r1cs::cheats::with_unchecked_prover` makes the prover skip its
own checks, so that a soundness test can check that the verifier rejects the result.

The `secp256k1` feature (this fork) adds the curve secp256k1 (see [Curves](#curves)).

## Curves

Every proof of the crate (range, linear, aggregated range proofs, R1CS and the circuit
builder on both backends, all of Bulletproofs++) runs over **ristretto255** (the default,
byte-identical to upstream) or, with the `secp256k1` feature, over **secp256k1** (on
[k256](https://crates.io/crates/k256)). The curve is a type parameter that defaults to
ristretto255 and is inferred from the generators:

```rust,ignore
use bulletproofs::secp256k1::{BulletproofGens, PedersenGens, RangeProof};

let pc_gens = PedersenGens::for_curve();          // B = H of secp256k1-zkp, B_blinding = G
let bp_gens = BulletproofGens::for_curve(64, 1);
let (proof, committed) = RangeProof::prove_single(&bp_gens, &pc_gens, &mut transcript, v, &blinding, 64)?;
```

- `bulletproofs::secp256k1` names the types over secp256k1 (`RangeProof`, `r1cs::Prover`,
  `bppp::RangeProof`, ...); generically, `RangeProof<C>`, `Prover<'g, T, C>`,
  `bppp::CircuitProof<C>` with `C: curve::Curve`.
- `new` and `default` constructors are the ristretto255 ones; `for_curve` is generic.
  `Verifier::new` is ristretto255, `Verifier::<_, C>::for_curve` any curve.
- Encodings on secp256k1: points are SEC1 compressed (33 bytes, the identity 33 zero bytes),
  scalars 32 bytes big-endian. A proof of one curve does not parse as the other, and every
  transcript of a curve other than ristretto255 absorbs the curve's name.
- Commitments to secrets go through k256's constant-time multiscalar multiplication
  (`lincomb`, GLV); public scalars through a variable-time Pippenger with batch-affine bucket
  sums. As upstream on ristretto255, the inner-product argument (and the BP++ norm argument
  with `bppp-vartime`) handles its blinded vectors `l(x)`, `r(x)` in variable time.
- Gadgets for both curves: `fn g<F: Field, CS: CircuitBuilder<F>>` (see
  [Writing gadgets for both backends](#writing-gadgets-for-both-backends)).

Proof sizes and times on one core of an Apple M4 Pro
(`cargo run --release --example curves_table --features "yoloproofs bppp secp256k1"`; R1CS:
a chain of multiplications):

| curve | proof | backend | size | prove | verify |
|---|---|---|---|---|---|
| ristretto255 | range 64 bits | BP | 672 B | 4.29 ms | 571 µs |
| ristretto255 | range 64 bits | BP++ | 416 B | 2.09 ms | 313 µs |
| ristretto255 | R1CS 2^10 | BP | 1057 B | 69.16 ms | 5.88 ms |
| ristretto255 | R1CS 2^14 | BP | 1313 B | 1.02 s | 73.20 ms |
| ristretto255 | R1CS 2^10 | BP++ | 817 B | 68.73 ms | 4.14 ms |
| ristretto255 | R1CS 2^14 | BP++ | 1073 B | 1.08 s | 53.26 ms |
| secp256k1 | range 64 bits | BP | 688 B | 14.50 ms | 1.55 ms |
| secp256k1 | range 64 bits | BP++ | 426 B | 3.08 ms | 572 µs |
| secp256k1 | R1CS 2^10 | BP | 1085 B | 151.67 ms | 9.83 ms |
| secp256k1 | R1CS 2^14 | BP | 1349 B | 2.18 s | 83.23 ms |
| secp256k1 | R1CS 2^10 | BP++ | 837 B | 127.61 ms | 5.78 ms |
| secp256k1 | R1CS 2^14 | BP++ | 1101 B | 2.00 s | 51.09 ms |

Proving on secp256k1 is 1.5–3.5 times slower (most for the small BP range proof, about twice
for circuits): k256's constant-time multiscalar multiplication costs 12.7 µs per term against
7.1 for curve25519-dalek (2^14 terms). Verification is closer (variable time: 2.3 against
1.8 µs per term at 2^14, 1.8 against 1.8 at 2^17; small multiplications are slower).

### Elements commitments

`bulletproofs::elements` (feature `secp256k1`) follows Elements / secp256k1-zkp, so the
proofs can be about values committed in Liquid confidential transactions:
`generator_generate(_blinded)` (asset generators, the Shallue–van de Woestijne map),
`h()` (secp256k1-zkp's default value generator H; Liquid commits values with the asset's
generator instead), `commit(value, blinding, gen)` = `value * gen + blinding * G`,
and the 33-byte encodings of generators (0x0a/0x0b) and commitments (0x08/0x09, the prefix
carrying the quadratic residuosity of y). `PedersenGens::with_value_generator(gen)` makes
the range proofs (BP and BP++) prove the value of such a commitment:

```rust,ignore
use bulletproofs::secp256k1::{elements, BulletproofGens, PedersenGens, RangeProof};

let asset = elements::generator_parse(&asset_generator_33_bytes).unwrap();  // blinded asset tag
let pc_gens = PedersenGens::with_value_generator(asset);
let committed = elements::commitment_parse(&commitment_33_bytes).unwrap();
// the prover knows (value, blinding) with committed = value * asset + blinding * G
let (proof, v) = RangeProof::prove_single(&bp_gens, &pc_gens, &mut transcript, value, &blinding, 64)?;
assert_eq!(v, bulletproofs::curve::Secp256k1::compress(&committed));
```

The key of `generator_generate` is the asset ID in internal byte order, the reverse of the hex
Elements displays. The BP range proof does not absorb the value generator into its transcript
(BP++ does): append the asset generator to the transcript before proving and verifying.

These are compatible commitments, not compatible proofs: the proofs are this crate's (BP or
BP++ with Merlin transcripts), not Elements' own range proof format.

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
- `bppp::CircuitProof::{prove, verify}`, arithmetic circuits (paper §5, spec §3): `w_L ∘ w_R = W_m w + f_m w_V + a_m`,
  `W_l w + f_l w_V + a_l = 0` with sparse matrices, a partition of `w_O` and committed input
  vectors (`BpppGens::commit_input`; a single value is an ordinary `PedersenGens` commitment).
  The generators come from the same `PedersenGens` and `BulletproofGens` as the BP backend.
  The transcript binds the dimensions, the generators `G` and `H_0`, a SHA3 digest of the
  circuit and the inputs. The Rust prover reproduces the independently written circuit part of
  the Python reference (`tests/vectors/bppp/circuit.json`) commitment for commitment.

- `bppp::ReciprocalProof::{prove, prove_two_phase, verify}`, reciprocal form circuits (paper
  §6.2–6.3, spec §4): private poles
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
  constraint system is lowered to a reciprocal form circuit (spec §6.1, the same lowering and one
  proof encoding with or without `CircuitBuilder` operations); randomized constraints are not
  supported on BP++ (they return a `GadgetError`).

- `r1cs::CircuitBuilder` (spec §7): free witnesses, products, public tables with lookups and
  general reciprocal (logUp-style) arguments on top of `ConstraintSystem`, implemented by
  `Prover` and `Verifier` for both backends. A gadget is written once: BP lowers it to
  randomized constraints (one second-phase multiplier per lookup, `|T|/2` multipliers per
  table), BP++ to a reciprocal form circuit (one gate per lookup, witnesses and multiplicities
  in free slots). Multi-column tuples are compressed with a challenge on both backends (BP:
  logUp's; BP++: a challenge `eta` after the components are committed, spec §4.7), so a lookup
  proves the tuple is a row component by component, with no range checks on the components.
  `cost()` reports the multipliers, gates and generator capacity of either backend.

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

Verification is about a third faster and proofs about a fifth smaller (these rows predate the
prover optimisations; see the large circuits below).

The circuit builder, $n$ committed values range-checked to 32 bits through a byte table (four
lookups each; `cargo bench --features "bppp yoloproofs" --bench bppp -- builder`; this machine,
4 cores, measured single-threaded):

| $n$ | proof BP++ / BP | prove BP++ / BP | verify BP++ / BP |
|---|---|---|---|
| 64 | 753 / 1089 B | 109 / 97 ms | 11.7 / 9.4 ms |
| 1024 | 945 / 1345 B | 1.13 / 1.26 s | 75 / 119 ms |

At small $n$ BP++ pays for its linear slots: witnesses and multiplicities beyond the
$N_p + N_m$ norm slots lengthen $H$.

Large circuits (`examples/bppp_profile.rs`, one process per row for the peak memory; Xeon
2.1 GHz, one thread; *vt* = feature `bppp-vartime`):

| circuit | proof BP / BP++ | prove BP / BP++ / BP++ vt | verify BP / BP++ | peak RSS BP / BP++ |
|---|---|---|---|---|
| R1CS, 2^18 multipliers | 1569 / 1329 B | 40.4 / 44.3 / 33.3 s | 3.50 / 2.68 s | 360 / 475 MB |
| R1CS, 2^20 multipliers | 1697 / 1457 B | 176 / 171 / 129 s | 15.7 / 11.5 s | 1238 / 1819 MB |
| builder, 2^14 × range32 | 1601 / 1201 B | 20.3 / 17.2 / 14.1 s | 1.88 / 1.20 s | 100 / 165 MB |
| builder, 2^16 × range32 | 1729 / 1329 B | 78.2 / 70.5 / 55.4 s | 7.38 / 4.68 s | 390 / 614 MB |

`BatchVerifier` checks many proofs in one multiplication (128 × 64-bit range proofs: 111 ms
instead of 168 ms one by one).

Apple M4 Pro, single-threaded, `rustc 1.99.1`, release profile.

## Writing gadgets for both backends

A gadget is a function that adds variables and constraints to a constraint system. In this
fork the same gadget code is proven with Bulletproofs (BP) or Bulletproofs++ (BP++), chosen per
proof with `set_backend`. The complete example below is `tests/guide.rs`.

### The traits

| trait | operations | backends |
|---|---|---|
| `ConstraintSystem` (upstream) | `multiply(l, r)`, `allocate(v)`, `allocate_multiplier(l, r)`, `constrain(lc)`, `metrics()` | both |
| `RandomizableConstraintSystem` (upstream) | `specify_randomized_constraints(f)`: a second phase with challenges | **BP only** |
| `CircuitBuilder` (this fork, spec §7) | `witness(v)`, `constrain_product(l, r, out)`, `table(rows)`, `lookup(t, tuple)`, `lookup_value(t, v)`, `reciprocal(m)` with `Reciprocal::{add, sub, add_weighted, add_public}`, `cost()` | both |

`CircuitBuilder: ConstraintSystem`, and both are implemented by `Prover` and `Verifier`, so
one gadget mixes plain R1CS and builder operations on the same variables, and existing
gadgets keep working unchanged. `CircuitBuilder` is object safe (`&mut dyn CircuitBuilder`).

All three traits take the scalar field as a parameter that defaults to ristretto255's:
`ConstraintSystem<F = Scalar>`, `CircuitBuilder<F = Scalar>`. A gadget written as
`fn g<CS: CircuitBuilder>(..)` is a ristretto255 gadget, as before; one written as
`fn g<F: Field, CS: CircuitBuilder<F>>(..)` (with `bulletproofs::curve::Field`) runs on every
curve. In generic code:

- values are `F::from(u64)`, linear combinations `LinearCombination<F>`;
- `lc ± var`, `lc ± F`, `lc ± u64`, `lc * F`, `var * F`, `var ± lc` and `var ± F` are
  generic;
- `var ± var`, `-var`, `var ± u64`, `var * u64` (any integer width) and `Scalar ± * var`
  produce ristretto255 linear combinations (they do not name a field): write `lc(a) + b`
  with `bulletproofs::r1cs::lc`;
- `Prover::new(&pc, ..)` takes its curve from the Pedersen generators;
  `Verifier::new(..)` is the ristretto255 verifier, `Verifier::<_, C>::for_curve(..)` the one
  over `C`.

### One gadget, two roles

The prover passes the values (`Some(v)`), the verifier `None`; both must issue the same
operations in the same order. Committed values come from `Prover::commit(v, blinding)` /
`Verifier::commit(V)` before the gadget runs and are passed in as `Variable`s.

```rust,ignore
/// `x < 2^16`: two byte lookups. `v` is the prover's value (`None` for the verifier).
fn range16<F: Field, CS: CircuitBuilder<F>>(cs: &mut CS, t: &Tables, x: LinearCombination<F>, v: Option<u64>) -> Result<(), R1CSError> {
    let lo = cs.lookup_value(t.byte, v.map(|v| v & 0xff))?;
    let hi = cs.lookup_value(t.byte, v.map(|v| v >> 8))?;
    cs.constrain(x - lo - hi * F::from(256u64));
    Ok(())
}

/// `z = x ^ y` for nibbles: one lookup of the tuple `(x, y, z)`; no range checks of the
/// components are needed (the lookup proves the tuple is a row, component by component).
fn xor4<F: Field, CS: CircuitBuilder<F>>(cs: &mut CS, t: &Tables, x: Variable, y: Variable, v: Option<(u64, u64)>) -> Result<Variable, R1CSError> {
    let z = cs.witness(v.map(|(a, b)| F::from(a ^ b)))?;
    cs.lookup(t.xor, &[x.into(), y.into(), z.into()])?;
    Ok(z)
}

/// `output` is a permutation of `input`: sum 1/(X + x) - sum 1/(X + y) = 0.
fn shuffle<F: Field, CS: CircuitBuilder<F>>(cs: &mut CS, input: &[Variable], output: &[Variable]) -> Result<(), R1CSError> {
    let arg = cs.reciprocal(1)?;
    for x in input {
        arg.add(cs, &[(*x).into()])?;
    }
    for y in output {
        arg.sub(cs, &[(*y).into()])?;
    }
    Ok(())
}
```

Proving and verifying (the tables are created once per statement and shared by all lookups):

```rust,ignore
let mut transcript = Transcript::new(b"guide");
transcript.append_u64(b"product", product); // public data not in the constraints
let mut prover = Prover::new(&pc, &mut transcript);
prover.set_backend(Backend::Bppp);
let (ca, va) = prover.commit(Scalar::from(a), blinding_a);
// ... statement(&mut prover, ...)
let bp = BulletproofGens::new(prover.cost().gens_capacity(Backend::Bppp), 1);
let proof = prover.prove(&bp)?;

let mut verifier = Verifier::new(&mut transcript_v);
verifier.set_backend(proof.backend()); // or require one backend
let va = verifier.commit(ca);
// ... the same statement(&mut verifier, ...), with None for the values
let bp = BulletproofGens::new(verifier.cost().gens_capacity(proof.backend()), 1);
verifier.verify(&proof, &pc, &bp)?;
```

`set_backend` may be called at any time before `prove`/`verify`: the builder only records
operations and lowers them at the end (BP: randomized constraints, spec §7.5; BP++: a
reciprocal form circuit, §7.6). A proof says which backend made it (`R1CSProof::backend`, and
`Backend` parses from and prints as `"bp"` / `"bppp"`); a verifier set to the other backend
rejects it. Accepting either backend means trusting both.

### What things cost

| operation | BP | BP++ |
|---|---|---|
| `multiply`, `allocate_multiplier` | 1 multiplier | 1 gate |
| `allocate` | ½ multiplier | ½ gate (paired into a real gate; reading its wire in a tuple or numerator costs a linear slot) |
| `witness`, `lookup_value`'s witness | ½ multiplier | no gate (a free slot of `w_O`: a spare output slot of a gate, else a linear slot) |
| `constrain_product(l, r, out)` | 1 multiplier (as `multiply` + `constrain`) | 1 gate, no linear rows |
| `constrain(lc)` | free (a row of the randomized combination) | free |
| `lookup` | 1 second-phase multiplier | 1 gate (+ a linear slot per component that reads a multiplier wire, for 2+ columns) |
| a table with lookups | `\|T\|/2` multipliers (multiplicities) | `\|T\|` linear slots |
| a term of a reciprocal argument | 1 second-phase multiplier | 1 gate (+ linear slots for copies, as for `lookup`) |
| a public term (`add_public`) | free | free |

`cost()` reports both (`gates(backend)`, `linear(backend)`, `gens_capacity(backend)`);
the verifier can compute it without the witness. BP's capacity is the multipliers rounded up
to a power of two, plus your own randomized multipliers, which `cost()` does not count. BP++'s
is `max(gates, linear + 6)`. Proof size grows with the logarithm of both. `metrics()` counts
only the plain R1CS part.

### Rules and pitfalls

- **Phases.** Builder operations belong to the first phase, and every variable they read must
  already exist. **BP++ refuses `specify_randomized_constraints`** (a `GadgetError` from the
  prover and the verifier): write permutations, lookups and multiset checks with `table`,
  `lookup` and `reciprocal`, not with your own challenges.
- **Tuples need no range checks.** Both backends compress a tuple with a challenge drawn after
  its components are committed. A lookup therefore proves the tuple *is* a row, whatever the
  components are. A reciprocal argument proves that its terms cancel per tuple (a multiset
  equality).
- **Tables.** Rows are public `u64`s. A table without lookups costs nothing. Create each table
  once and share it: its multiplicities are paid once per table.
- **Reciprocal arguments** are recorded when `reciprocal(m)` is called; terms are validated
  as they are added; an argument without terms adds nothing.
- **What the prover refuses.** Errors appear at `prove`, not at the operation:

  | witness fault | BP prover | BP++ prover |
  |---|---|---|
  | lookup equal to no row | `GadgetError` | `GadgetError` |
  | unsatisfied multiplication or reciprocal argument | a proof that does not verify | refused |
  | violated linear constraint | a proof that does not verify | a proof that does not verify |

- **Binding.** BP++ binds a digest of the lowered circuit; BP does not hash the constraint
  system. Absorb public statement data that the constraints do not contain into the
  transcript before `Prover::new` (as `product` above).
- **Constant time.** Computing the witness values in your gadget is your code: keep it constant
  time in the secrets. The builder's own multiplicity counting is constant time.
- **Compatibility.** `Variable::Witness` is a new variant: exhaustive `match`es on `Variable`
  in downstream code need an arm for it.

### Testing

Use `Prover::prove_with_rng` for deterministic proofs. To test soundness, prove false
statements with the testing feature `cheats`:
`r1cs::cheats::with_unchecked_prover(|| prove(...))` makes the prover skip its own checks
(lookups equal to no row, unsatisfied BP++ circuits), and the verifier must reject the result.
bpvm (github.com/juja256/bpvm) is a larger example: an RV32IM zkVM written once against
`CircuitBuilder` and proven with either backend.

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

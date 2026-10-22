# Simplicity verifier (experimental)

Feature `simplicity` (implies `secp256k1`, `bppp`, `yoloproofs`). An R1CS circuit on the BP++
backend over secp256k1, with the [SHA-256 transcript](sha256-transcript.md), compiles into a
[Simplicity](https://github.com/BlockstreamResearch/simplicity) program that verifies its proofs
and is bound to the spending transaction. The program runs as a Liquid node would run it. Stage 1
made this work end to end; stage 2 made it several times cheaper; stage 3 recomputes instead of
storing and fits about 950 gates in a standard transaction; stage 4 picks the lightest of several
lowerings and stops a quadratic blow-up on lookup tables (see [Measurements](#measurements)). The design
follows [simple-groth16](https://github.com/BlockstreamResearch/simple-groth16), which generates a
Groth16 verifier for Simplicity.

## What the program checks

- **Witness.** The witness holds the proof: its points as (parity of y, x) and its scalars as
  256-bit words.
- **Points.** Every point is decompressed (`decompress`; a point not on the curve fails), and every
  scalar must be canonical (below the group order).
- **Transcript.** The program recomputes the verifier's transcript with the `sha_256_ctx_8_*` jets:
  - the records before the transaction hash are constant, so the program starts from their
    midstate;
  - the record under `SIGHASH_LABEL` takes `jet_sig_all_hash`;
  - points enter in their SEC1 encoding.
- **Challenges** come from 64 bytes: `normalize(o0) · R + normalize(o1)`, `R = 2^256 mod n`.
- **Scalar arithmetic.** The program repeats the BP++ verifier's scalar arithmetic: the reciprocal
  form's compilation with its challenges, the weights, the polynomials, and the norm argument's
  scalars. Its checks ("not zero") are assertions.
- **Final equation.** The program checks it as one multiscalar multiplication (`scale` and
  `gej_add` per term) equal to the point at infinity.
- **Constants.** The circuit, the generators and the commitments `V` are constants of the program:
  one program, and so one address (its CMR), per circuit and statement.

## How the program is built

The compiler traces the crate's own BP++ verifier (`reciprocal::terms`):

- It runs the verifier on a dummy proof of the circuit's dimensions, over a scalar type that records
  every operation on a tape and a curve whose points remember whether they come from the proof.
  Operations on constants fold. A scalar from the proof or a challenge starts a node.
- The tracer tells proof data from constants by their bytes. The dummy proof is therefore drawn
  at random for every compilation, so that no statement can be crafted to equal one of its
  points; the compiler also refuses a statement or generator point equal to one. The program
  does not depend on the dummy proof.
- The verifier's control flow depends only on the circuit's shape. Its value-dependent checks
  become assertions, and an equality between two traced values is refused. A test traces two
  proofs and requires the same tape.
- The tape, the transcript's records and the final multiscalar multiplication are lowered to a
  small SSA IR (`src/simplicity/ir.rs`), then to a DAG of Simplicity combinators built straight into
  rust-simplicity nodes (no text to parse; `to_text` writes the text on demand).
- **IR passes** (`src/simplicity/opt.rs`), exact in `F_n` and in the group:
  - a product becomes `c · Π a^e` over its atoms (challenges, inverses, witnesses, sums),
    built as a product of squares `a^(2^j)`, lowest first, so the powers of one atom share their
    prefixes (`mu^13` reuses `mu^5`) and every power is `O(log t)` deep;
  - chains of additions become balanced trees;
  - equal pure operations merge, and operations nobody needs go (checks, unwraps and witnesses
    stay).
- **Expression trees with recomputation.** A value read once is built inside its reader. A value
  read several times is either **stored** (a step of its own, kept in the environment) or
  **recomputed** inside each reader. A greedy pass from the last operation back decides, with
  rust-simplicity's costs: recompute when (times it runs) × (its own cost and that of the
  arguments only it reads) is at most (2 × its bits × the steps it would live) + (its reads).
  A witness run more than once, a transcript state read more than once and a hash read from a
  state are always stored.
- **Signed exponents.** `invert(x)` of a monomial of one atom, or of atoms whose inverses are
  built already, is a monomial with the exponents negated (`μ^-1` of `μ = ρ²` is `ρ^-2`); the
  inverse of a product of several atoms stays one `invert` (a batch inversion keeps its single
  inversion). An exponent is written in its non-adjacent form when that has fewer digits than
  the binary one, counting a new `invert(a)` as 4 products: a positive digit takes `a^(2^j)`, a negative one
  `invert(a)^(2^j)`. A third of the bits are digits on average instead of half, so a
  recomputed power takes fewer products (`μ^63 = μ^64 · μ^-1`: one product instead of five).
  Exact for `a = 0` too: every such product has a factor 0, and an exponent that cancels to 0
  stays as the factor `a · invert(a)`, 0 for `a = 0` (`invert(0) = 0`).
- **A product of more than 8 distinct atoms** (a prefix product of a batch inversion over a
  lookup table) is kept as the tape built it: rebuilding each from its atoms was quadratic.
- **The lightest of several programs.** The compiler builds the program with the generators as
  constant points and as x and parity (`decompress`, 32 bytes fewer, 10.9 WU more per term),
  lowers each with 1, 2 or 3 passes deciding the roles (each after the first counts the
  arguments the previous one inlined) and with or without a hot/cold environment (the values
  read most in a small tree), then tries small constant words (a word with a zero half as the
  pair of its halves) and shared functions (a value inlined in several steps as one function of
  its stored inputs) on the best. It weighs each without running it (the dummy proof's witness
  has the real one's types, so the unpruned program has the same bytes and static cost as with a
  real proof; the pruned program a node runs differs by about 32 bytes per selection), drops any
  that needs more cells than consensus allows, and keeps the smallest max(budget, cost):
  byte-bound programs choose fewer bytes, cost-bound ones a lower cost. `Stats::lowering` names
  the choice, on which the CMR depends.
- **The multiscalar multiplication is a balanced tree** of `gej_add`; with the coefficients
  recomputed where they are read, the whole sum is one expression over the stored values.
- **Scheduling.** Steps are ordered to keep few bits alive: on demand from each sink, deepest
  dependency first (the best of that, a greedy order and the program order, by the total of live
  bits).
- **The environment** of a step is a binary tree of slots. A value holds a slot from its step to
  the last step that reads it, a read is a path of `log2(slots)` selectors, and a step rebuilds
  only the paths to the slots it changes.

The cost model this follows (rust-simplicity's static bound): every executed combinator costs 100
mWU, `iden` and `comp` also pay the width of the value they copy, `take` and `drop` nothing more,
and a jet its fixed price. A read deep in a list environment was therefore a long chain of
`drop`s; a step copies the values that stay alive.

## Use

The prover appends the transaction's hash under `SIGHASH_LABEL`, and the compiler appends a
placeholder at the same place:

```rust,ignore
use bulletproofs::simplicity::{sighash_of, CompileTranscript, SIGHASH_LABEL};

// prover (the spending transaction's environment `env`)
let mut t = Sha256Transcript::new(b"app");
t.append_message(SIGHASH_LABEL, &sighash_of(&env));
let mut prover = Prover::new(&pc_gens, &mut t);
prover.set_backend(Backend::Bppp);
// ... commit, gadgets ...
let proof = prover.prove(&bp_gens)?;

// compiler: the same records, the same circuit
let mut ct = CompileTranscript::new(b"app");
ct.append_message(SIGHASH_LABEL, &[0; 32]);          // becomes jet_sig_all_hash
let mut v = Verifier::<_, Secp256k1>::for_curve(&mut ct);
v.set_backend(Backend::Bppp);
// ... commit(V), gadgets ...
let sv = v.compile_to_simplicity(&pc_gens, &bp_gens)?;
sv.cmr();                                              // the program's commitment (address)
let w = sv.witness(&proof)?;
sv.execute(&w, &env)?;                                 // as a node: cost, sizes, cells
```

The witness names are `p<i>` for the proof's points in the order of their bytes (`C_L, C_R, C_O,
C_S`, then `X_r, R_r` per round), as (parity bit, x), and `s<i>` for its final scalars.

The budget `execute` checks is the node's: 1000 · (witness stack + 50) mWU, where the stack holds
the witness data, the program, the CMR and the control block. It also checks consensus's cell
limit (5 242 880).

**Limitations.**
- Only BP++, without randomized constraints.
- A proof containing the identity point cannot be verified (probability about 2^-256 for an
  honest proof).
- `V` are constants.
- The program text is generated per circuit, and changing the generator changes the CMR.

## Measurements

Chains of `n` multiplications from one committed value
(`cargo run --release --example simplicity_costs --features simplicity [log2 max, default 10]`; Apple
M4 Pro, 2026-10-22, stage 4). The transaction weight of the input is its witness stack, or the
cost (in WU) if that is larger (padding). `stored`: steps that keep a value; `data`: the part of
the cost that copies data (`comp` and `iden`).

| gates | MSM terms | steps | stored | cost (mWU) | budget (mWU) | jets | data | program | B/gate | witness | cells | tx WU | compile | run |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 18 | 60 | 46 | 3 026 698 | 5 067 000 | 58% | 28% | 4 594 B | 2 297 | 353 B | 54 355 | 5.0 k | 57 ms | 25 ms |
| 4 | 22 | 68 | 56 | 3 800 126 | 5 955 000 | 57% | 29% | 5 482 B | 1 370 | 353 B | 53 103 | 5.9 k | 58 ms | 30 ms |
| 8 | 26 | 78 | 65 | 4 809 938 | 7 558 000 | 55% | 30% | 7 053 B | 881 | 385 B | 62 831 | 7.5 k | 68 ms | 38 ms |
| 16 | 36 | 96 | 84 | 7 317 834 | 10 638 000 | 52% | 31% | 10 100 B | 631 | 418 B | 81 275 | 10.6 k | 0.10 s | 55 ms |
| 32 | 52 | 130 | 116 | 11 800 759 | 16 926 000 | 48% | 34% | 16 324 B | 510 | 482 B | 129 607 | 16.9 k | 0.16 s | 86 ms |
| 64 | 86 | 201 | 187 | 23 913 795 | 29 723 000 | 42% | 39% | 29 057 B | 454 | 546 B | 208 224 | 29.7 k | 0.30 s | 161 ms |
| 128 | 152 | 273 | 259 | 48 730 005 | 54 247 000 | 40% | 36% | 53 517 B | 418 | 610 B | 296 574 | 54.2 k | 0.57 s | 0.3 s |
| 256 | 282 | 314 | 300 | 97 964 949 | 97 946 000 | | | | | | | ≈ 98.0 k (padded) | 1.0 s | 0.6 s |
| 512 | 540 | 353 | 339 | 193 598 601 | 191 784 000 | | | | | | | ≈ 193.6 k (padded) | 1.9 s | 1.3 s |
| 1 024 | 1 054 | 389 | 375 | 398 755 769 | 379 894 000 | | | | | | | **≈ 398.8 k (padded): fits** | 3.6 s | 2.6 s |

Stage 3 against stage 4 (input weight):

| circuit | stage 3 | stage 4 |
|---|---|---|
| chain 16 | 11.3 kWU | 10.6 kWU |
| chain 64 | 32.2 kWU | 29.4 kWU |
| chain 256 | 111.1 kWU | 100.9 kWU |
| chain 512 | 209.0 kWU | 193.6 kWU (padded) |
| chain 1 024 | 430.7 kWU (padded) | **398.8 kWU (padded): fits** |
| lookup table of 256 rows, 8 lookups (`tests/simplicity.rs`) | ≈ 314 kWU | 70.2 kWU |
| bpvm `mul` (776 gates, 1 660 MSM terms) | ≈ 2 170 kWU | 574 kWU |
| bpvm fib (2 450 gates, 4 165 MSM terms) | ≈ 3 550 kWU | 1 480 kWU |
| bpvm `mul`, trimmed circuit (384 gates, 990 MSM terms) | 773 kWU | **299.2 kWU (padded): fits** |
| bpvm fib, trimmed circuit (1 919 gates) | | 1 101 kWU (padded) |

bpvm's trimmed circuit (bpvm branch `circuit-trim`: the stack sized when the guest is linked,
timestamp gaps sized by the step count, only the registers the program names) brings `mul`
below the 400 kWU of a standard transaction. The VM rows gain most from the bound on monomials: a lookup table's batch inversion made the
IR of bpvm's `mul` grow from 42 721 to 230 041 operations; it now stays at 46 198. The program
choice brings the rest. The compiler builds 19 programs (18 candidates and the winner again),
weighing the candidates on 4 threads by default (`simplicity::set_compile_threads`; 0 for every
core); the table's compile times are on 4 threads. The program does not depend on the threads:
the choice is the first lightest in a fixed order. Each thread holds one candidate, so threads
trade memory for time: bpvm's fib compiles in 26 s on 1 thread (1.5 GB), 10 s on 4 (3.4 GB), 7 s
on 8 or more (6 to 7.5 GB).

Earlier: stage 2 against stage 3 (same chains):

| gates | stage 2 cost | stage 3 cost | stage 2 program | stage 3 program | stage 2 tx | stage 3 tx |
|---|---|---|---|---|---|---|
| 16 | 9.7 M mWU | 6.7 M | 15.7 kB | 10.8 kB | 16.2 k | 11.3 k |
| 64 | 50.6 M | 20.0 M | 50.4 kB | 31.6 kB | 51.0 k | 32.2 k |
| 256 | 522.8 M | 89.7 M | — | 110.4 kB | ≈ 523 k (padded) | 111.1 k |
| 512 | over the cell limit | 199.5 M | — | 208.2 kB | — | 209.0 k |

Where the cost of 64 gates went (rust-simplicity's static bound split by kind of node): stage 2
spent 73% copying the environment between steps (Σ live bits 17.3 M); stage 3 spends 35% (Σ
live bits 1.3 M), 31% on `scale` and 10% on recomputed products.

**bpvm's fib on secp256k1** (bpvm feature `simplicity`, `examples/simplicity.rs`): 78 steps,
2 450 BP++ gates, 1 683 linear slots, 4 165 MSM terms and 81 613 traced operations. Stage 2
needed 37 M cells; stage 3 ran it in 1.46 M cells, 2.8 G mWU and a 3.55 MB program; stage 4
compiles it in 34 s and runs it in 9 s: 1.48 G mWU (padded weight 1 480 kWU), a 1.43 MB program.
Running it for the first time found a bug
in bpvm, not here: `vm::simplicity::prove` bound the statement to the transcript twice and
`compile` once, so its honest proofs were rejected (fixed in bpvm `da59f07`, with a test that runs
the verifier). bpvm's `mul` guest (c = a · b with private a, b; 18 steps, 776 gates, 852 linear
slots, 1 660 MSM terms) runs too: stage 3 gave 1.55 G mWU and a 2.17 MB program, stage 4 gives
571 M mWU and a 573 kB program (574 kWU) in 1.41 M cells. The VM's fixed
tables and dense linear constraints, not the multiplication, make it large; the same statement
as a direct R1CS circuit (`x · y = 15` in the tests) is about 5 kWU.

**What this says.**

- The chain of 1 024 gates fits a standard transaction (400 kWU): its cost (398.8 M mWU) passes
  its budget, so the input is padded to about 398.8 kWU, 0.3% under the limit. From 256 gates
  the cost sets the weight; below, the bytes.
- The jets of the multiscalar multiplication (`scale` and `gej_add`, about 77 WU per term with a
  minimal coefficient) put the ceiling of a standard transaction near 5 000 gates; at 512 gates
  both the cost (390 WU per gate) and the bytes (406 B per gate) are about 5× above that floor.
- Recomputation trades copying for computation; on dense circuits (fib) the same value
  recomputed in many steps is written as code in each, since its paths differ step by step.
- **Comparison with [simple-groth16](https://github.com/BlockstreamResearch/simple-groth16):** its
  Groth16 verifier costs 48.6 M mWU, a 53 kWU transaction, for any circuit. BP++ is now lighter
  up to about 100 gates and heavier above. A circuit of bpvm's size (fib) does not fit a standard
  transaction even at the floor of jets and generators (about 400 kWU). BP++ in Simplicity suits
  small statements, without a trusted setup, about secp256k1 commitments (Liquid's confidential
  amounts and assets).

## Next

- **Verify the sum with hints** (not done): `point_verify_1` checks `a·A + b·G = C` for 41.5 k mWU
  against 72.7 k for `scale`; with the prover's points `D_i = k_i·P_i` in the witness, about −20 WU
  and +33 B per term, for cost-bound programs.

- **Blocks of the sum (tried, not kept).** Lowering a subtree of 16 or 64 terms over a tuple of
  what it reads and of the scalars it would compute more than once (computed once per block)
  cuts the cost of the chain of 1 024 gates by 19% (411 → 332 M mWU) but adds 45–50% bytes: a
  node's identity (IHR) includes its input type, so code is no longer shared between blocks.
  It would pay only where the cost far exceeds the bytes.
- Bind the commitments `V` to the transaction's outputs, and compile the BP backend.

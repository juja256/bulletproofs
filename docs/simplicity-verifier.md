# Simplicity verifier (experimental)

Feature `simplicity` (implies `secp256k1`, `bppp`, `yoloproofs`). An R1CS circuit on the BP++
backend over secp256k1, with the [SHA-256 transcript](sha256-transcript.md), compiles into a
[Simplicity](https://github.com/BlockstreamResearch/simplicity) program that verifies its proofs
and is bound to the spending transaction. The program runs as a Liquid node would run it. Stage 1
made this work end to end; stage 2 made it several times cheaper; stage 3 recomputes instead of
storing and fits about 950 gates in a standard transaction (see [Measurements](#measurements)). The design
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
M4 Pro, 2026-10-21, stage 3). The transaction weight of the input is its witness stack, or the
cost (in WU) if that is larger (padding). `stored`: steps that keep a value; `data`: the part of
the cost that copies data (`comp` and `iden`).

| gates | MSM terms | steps | stored | cost (mWU) | budget (mWU) | jets | data | program | B/gate | witness | cells | tx WU | compile | run |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 18 | 60 | 46 | 2 831 682 | 5 420 000 | 57% | 30% | 4 947 B | 2 473 | 353 B | 54 355 | 5.4 k | 10 ms | 36 ms |
| 4 | 22 | 66 | 54 | 3 554 123 | 6 315 000 | 57% | 30% | 5 842 B | 1 460 | 353 B | 53 615 | 6.3 k | 9 ms | 31 ms |
| 8 | 26 | 74 | 61 | 4 524 003 | 7 983 000 | 54% | 30% | 7 478 B | 934 | 385 B | 61 807 | 7.9 k | 11 ms | 39 ms |
| 16 | 36 | 90 | 78 | 6 693 380 | 11 303 000 | 52% | 31% | 10 765 B | 672 | 418 B | 81 531 | 11.3 k | 15 ms | 56 ms |
| 32 | 52 | 115 | 101 | 10 713 032 | 18 418 000 | 49% | 32% | 17 816 B | 556 | 482 B | 111 686 | 18.4 k | 25 ms | 91 ms |
| 64 | 86 | 159 | 145 | 20 042 079 | 32 243 000 | 45% | 35% | 31 577 B | 493 | 546 B | 199 520 | 32.2 k | 49 ms | 174 ms |
| 128 | 152 | 221 | 207 | 41 309 307 | 61 626 000 | 41% | 36% | 60 896 B | 475 | 610 B | 317 296 | 61.6 k | 96 ms | 0.3 s |
| 256 | 282 | 284 | 270 | 89 711 575 | 111 193 000 | 40% | 34% | 110 399 B | 431 | 674 B | 477 840 | 111.1 k | 169 ms | 0.7 s |
| 512 | 540 | 334 | 320 | 199 465 509 | 209 011 000 | 39% | 30% | 208 152 B | 406 | 739 B | 580 770 | 209.0 k | 0.3 s | 1.4 s |
| 1 024 | 1 054 | 391 | 377 | 429 518 649 | 403 223 000 | | | | | | | ≈ 430 k (padded) | 0.6 s | 2.8 s |

Stage 2 against stage 3 (same chains):

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
needed 37 M cells. Stage 3 compiles it in 4 s and runs it as a node in 18 s: 1.46 M cells (within
the limit), 2.8 G mWU (26% data), and a 3.55 MB program. Running it for the first time found a bug
in bpvm, not here: `vm::simplicity::prove` bound the statement to the transcript twice and
`compile` once, so its honest proofs were rejected (fixed in bpvm `da59f07`, with a test that runs
the verifier). bpvm's `mul` guest (c = a · b with private a, b; 18 steps, 776 gates, 852 linear
slots, 1 660 MSM terms) runs too: 1.04 M cells, 1.55 G mWU, a 2.17 MB program. The VM's fixed
tables and dense linear constraints, not the multiplication, make it large; the same statement
as a direct R1CS circuit (`x · y = 15` in the tests) is about 5 kWU.

**What this says.**

- Up to 512 gates the weight is set by the program's bytes, not its cost (the witness stack is
  larger than the cost in WU), and the program fits a standard transaction (400 kWU) with no
  padding (209 kWU at 512 gates). At 1 024 gates the cost (429.5 M mWU) passes the budget, so the
  input needs padding to about 430 kWU: the limit is about 950 gates.
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

- **Bytes.** The program's size now sets the weight: share the code of a value recomputed in
  several steps (one function over the stored values it reads), store generators as `x` and
  parity (`decompress`, −32 B and +11 WU per point), and weigh bytes in the store/recompute rule.
- A hot/cold environment (values read often in a small tree) was tried: −1.2% of the cost at 64
  gates but more bytes, so it was left out.
- Bind the commitments `V` to the transaction's outputs, and compile the BP backend.

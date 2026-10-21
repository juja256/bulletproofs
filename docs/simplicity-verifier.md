# Simplicity verifier (experimental)

Feature `simplicity` (implies `secp256k1`, `bppp`, `yoloproofs`). An R1CS circuit on the BP++
backend over secp256k1, with the [SHA-256 transcript](sha256-transcript.md), compiles into a
[Simplicity](https://github.com/BlockstreamResearch/simplicity) program that verifies its proofs
and is bound to the spending transaction. The program runs as a Liquid node would run it. Stage 1
made this work end to end; stage 2 made it several times cheaper (see [Measurements](#measurements)). The design
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
- **Expression trees.** A value read once is built inside its reader, so it is written once,
  straight into its reader's input. A step is a value read several times (stored), a check, a
  value read by nobody, or a term of the multiscalar multiplication.
- **Scheduling.** Steps are ordered to keep few bits alive: on demand from each sink, deepest
  dependency first, so each term of the sum comes right after its coefficient (the best of that,
  a greedy order and the program order, by the total of live bits).
- **The environment** of a step is a binary tree of slots. A value holds a slot from its step to
  its last reader's, a read is a path of `log2(slots)` selectors, and a step rebuilds only the
  paths to the slots it changes.

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
(`cargo run --release --example simplicity_costs --features simplicity [log2 max]`; Apple M4 Pro). The
transaction weight of the input is its witness stack, or the cost (in WU) if that is larger
(padding).

| gates | MSM terms | steps | cost (mWU) | budget (mWU) | jets | program | witness | cells | tx WU | compile | run |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 18 | 84 | 3 103 445 | 6 625 000 | 52% | 6 152 B | 353 B | 48 997 | 6.6 k | 13 ms | 36 ms |
| 4 | 22 | 103 | 4 051 373 | 8 163 000 | 49% | 7 690 B | 353 B | 62 582 | 8.1 k | 10 ms | 33 ms |
| 8 | 26 | 133 | 5 478 297 | 10 195 000 | 43% | 9 690 B | 385 B | 100 672 | 10.1 k | 11 ms | 40 ms |
| 16 | 36 | 198 | 9 675 434 | 16 268 000 | 34% | 15 730 B | 418 B | 170 576 | 16.2 k | 19 ms | 66 ms |
| 32 | 52 | 300 | 19 483 906 | 27 012 000 | 25% | 26 410 B | 482 B | 335 450 | 27.0 k | 32 ms | 116 ms |
| 64 | 86 | 519 | 50 551 736 | 51 066 000 | 16% | 50 400 B | 546 B | 663 416 | 51.0 k | 62 ms | 256 ms |
| 128 | 152 | 946 | 153 699 950 | 102 131 000 | | | | | ≈ 154 k (padded) | 130 ms | 0.7 s |
| 256 | 282 | 1 789 | 522 822 464 | 213 543 000 | | | | | ≈ 523 k (padded) | 283 ms | 2.4 s |

Stage 1 against stage 2:

| gates | stage 1 cost | stage 2 cost | stage 1 program | stage 2 program | stage 1 compile + run | stage 2 |
|---|---|---|---|---|---|---|
| 8 | 22.3 M mWU | 5.5 M | 42.0 kB | 9.7 kB | 31.6 s + 31.8 s | 11 ms + 40 ms |
| 16 | 61.4 M | 9.7 M | 104.4 kB | 15.7 kB | 506 s + 545 s | 19 ms + 66 ms |
| 64 | over budget | 50.6 M (within) | — | 50.4 kB | — | 62 ms + 256 ms |

**bpvm's fib on secp256k1** (bpvm feature `simplicity`, `examples/simplicity_fib.rs`): 78 steps,
2 450 BP++ gates, 1 683 linear slots, 4 165 MSM terms and 81 613 traced operations. It compiles in
6.3 s, but the program needs 37 M cells (the limit is 5.24 M), and its jets alone (4 165 `scale`s,
about 80 000 scalar operations) cost about 370 M mWU, plus about 267 kB of generator constants.

**What this says.**

- Up to about 64 gates the program fits a standard transaction with no padding (51 kWU at 64
  gates). With padding, it fits to about 180 gates (the 400 kWU standard limit).
- The cost still grows faster than the circuit, now because of the live data itself. The
  verifier's matrix–vector products keep about `min(rows, columns)` values alive, and every step
  copies them (Σ live bits: 17.3 M at 64 gates).
- **Comparison with [simple-groth16](https://github.com/BlockstreamResearch/simple-groth16):** its
  Groth16 verifier costs 48.6 M mWU, a 53 kWU transaction, for any circuit. Here, BP++ is cheaper
  below about 64 gates and dearer above. A circuit of bpvm's size (fib) does not fit a standard
  transaction even at the floor of jets and generators (about 400 kWU). BP++ in Simplicity suits
  small statements, without a trusted setup, about secp256k1 commitments (Liquid's confidential
  amounts and assets).

## Next

- **Regroup the coefficients of the multiscalar multiplication** that are linear in shared values:
  `Σ_j (Σ_r W_rj u_r) H_j = Σ_r u_r (Σ_j W_rj H_j)`, with the inner sums constant points computed at
  compile time. That removes the matrix–vector products from the program, and with them the large
  live set.
- **Scoped blocks**: copy long-lived values once per block rather than once per step.
- Bind the commitments `V` to the transaction's outputs, and compile the BP backend.

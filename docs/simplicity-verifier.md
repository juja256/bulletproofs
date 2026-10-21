# Simplicity verifier (experimental, stage 1)

Feature `simplicity` (implies `secp256k1`, `bppp`, `yoloproofs`). An R1CS circuit on the BP++
backend over secp256k1, with the [SHA-256 transcript](sha256-transcript.md), compiles into a
[Simplicity](https://github.com/BlockstreamResearch/simplicity) program that verifies its proofs
and is bound to the spending transaction. The program runs as a Liquid node would run it. Stage 1
makes this work end to end; it is not yet cheap (see [Measurements](#measurements)). The design
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
  small SSA IR (`src/simplicity/ir.rs`). That IR becomes Simplicity's human-readable encoding: a
  chain of steps over an environment of the values still needed, ordered by last use, composed as
  a balanced tree. rust-simplicity 0.9 parses it, prunes it against the transaction and runs it.

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
(`cargo run --release --example simplicity_costs --features simplicity`; Apple M4 Pro):

| gates | tape ops | MSM terms | cost (mWU) | budget (mWU) | program | witness | cells | jets (mWU) | compile | run |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 121 | 18 | 8 507 765 | 16 395 000 | 15 922 B | 353 B | 84 995 | 1 615 817 | 1.8 s | 1.9 s |
| 4 | 177 | 22 | 13 437 957 | 27 625 000 | 27 152 B | 353 B | 110 852 | 1 994 727 | 6.8 s | 6.9 s |
| 8 | 274 | 26 | 22 254 683 | 42 509 000 | 42 004 B | 385 B | 167 680 | 2 373 801 | 31.6 s | 31.8 s |
| 16 | 474 | 36 | 61 444 862 | 104 969 000 | 104 431 B | 418 B | 280 654 | 3 319 902 | 506 s | 545 s |

`x · y = 15` with two commitments costs 8 412 334 mWU (program 16 020 B). A circuit with a table
lookup and a witness variable costs 36 264 635 mWU (budget 75 041 000).

**What this says.**

- **Everything fits.** Each program fits its budget: the program's own bytes pay for its cost,
  as in simple-groth16. Each also fits the cell limit.
- **Cost is mostly data movement.** The jets' fixed costs are 5–20% of the total. A step copies
  the live part of its environment, and that part grows with the circuit's vectors, so the cost
  grows faster than the circuit: 22.3M mWU at 8 gates, 61.4M at 16.
- **The program grows faster than the circuit too.** It is 42 kB at 8 gates and 104 kB at 16,
  because the tape is unrolled and every step rebuilds its environment. A 2^11-gate circuit would
  need megabytes, against a 400 kWU standard transaction. Stage 1 is a correct baseline, not a
  deployable verifier for large circuits.
- **Compiling and running grow much faster than linearly** (16× from 8 to 16 gates). Most of the
  time is spent parsing and type-checking the text.

## Stage 2 (next)

- Build the program's nodes directly (rust-simplicity's construction API) instead of text.
- Share repeated structure as functions: the multiscalar multiplication's term, the norm
  argument's rounds, rows of the circuit's weights.
- Lay the environment out so that a step moves only what it reads (as simple-groth16 packs
  operands and narrows environments).
- Bind the commitments `V` to the transaction's outputs, and compile the BP backend.

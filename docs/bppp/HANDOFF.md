# Bulletproofs++ in this fork: hand-off

State of the work, the method that produced it, the owner's rules, and the plan for what is
left. Written 2026-10-19 at the end of phase 5, for a session that continues without the
original context (the owner's notes live in a private knowledge base that the next session
cannot see). Keep the **Progress log** at the end up to date.

## Goal

A complete Bulletproofs++ (Eagen, Kanjalkar, Ruffing, Nick, ePrint 2022/510,
<https://eprint.iacr.org/2022/510>) behind the `bppp` feature: norm argument, arithmetic
circuits, reciprocal form circuits, range proofs, multi-asset transactions, a BP++ backend for
the existing R1CS front end, a circuit builder shared by both backends, performance work, and
then the zkVM `bpvm` (github.com/juja256/bpvm, a separate repository) on BP++.

## Status

| phase | what | where | state |
|---|---|---|---|
| 1 | weighted norm linear argument (WNLA) | `src/bppp/wnla.rs`, spec §2 | merged in `main`; aligned with secp256k1-zkp (`2690aaa`) |
| 2 | arithmetic circuits (paper §5) | `src/bppp/circuit.rs`, `gens.rs`, `poly.rs`, `sparse.rs`, spec §3 | branch `bppp-circuit` (pushed) |
| 3 | reciprocal form circuits (§6.2–6.3) | `src/bppp/reciprocal.rs`, spec §4 | branch `bppp-reciprocal` |
| 4 | range proofs, MACT (§6.4–6.5) | `src/bppp/range.rs`, `mact.rs`, spec §5 | branch `bppp-range` |
| 5 | R1CS front end on BP++ | `src/r1cs/backend.rs`, `proof.rs`, `prover.rs`, `verifier.rs`, spec §6 | branch `bppp-r1cs` (this one) |
| 6 | `CircuitBuilder` | — | next |
| 7 | performance and hardening | — | open |
| 8 | bpvm on BP++ | other repository | open |

The branches are stacked: `main` ⊂ `bppp-circuit` ⊂ `bppp-reciprocal` ⊂ `bppp-range` ⊂
`bppp-r1cs`. None of 2–5 is merged into `main` yet; ask the owner before merging.

Numbers (Apple M4 Pro, one thread): a 64-bit range proof is 416 B (paper's figure) against 672 B
for the BP `RangeProof`, proving in 2.55 vs 4.39 ms, verifying in 0.48 vs 0.61 ms; a circuit of
2^14 multiplications 1056 B vs 1313 B, verify 52 vs 77 ms, prove 1.10 vs 0.99 s (prover not yet
optimised); the same circuit through the R1CS front end on BP++ 817 B at 2^10.

## Map of the repository

- `docs/bppp/spec.md` — the normative specification (§1 conventions, §2 WNLA, §3 circuits,
  §4 reciprocal form, §5 range/MACT, §6 R1CS). The paper's typeset formulas in §5 are wrong in
  several places; the spec re-derives them. Implementations follow the spec, not the paper.
- `docs/bppp/bppp-paper-errors.tex` — errata of the paper (18 items, each with location,
  problem, fix and status Verified/Observed/Noted). A living document: add every inaccuracy you
  find. Build with `latexmk -pdf` outside the repository (aux files are git-ignored).
- `ref/bppp_ref.py` — spec-level Python reference (field arithmetic mod ℓ, symbolic group:
  points are maps generator → coefficient; challenges are inputs). `ref/gen_vectors.py` writes
  `tests/vectors/bppp/{wnla,circuit,reciprocal,range,mact}.json` deterministically.
  `ref/xcheck_secp256k1_zkp.py` runs the reference's norm argument over secp256k1 with
  secp256k1-zkp's transcript and reproduces their prove vectors byte for byte and their verify
  verdicts (13/13), from `tests/vectors/bppp/secp256k1-zkp/`.
- Rust tests: unit tests in each `src/bppp/*.rs` (including `matches_reference_vectors`, which
  replays the reference's randomness and challenges and compares every commitment);
  `src/bppp/testutil.rs` (vector helpers); `tests/r1cs_bppp.rs`; `tests/golden.rs` pins the BP
  proofs to upstream bytes (they must never change).
- `benches/bppp.rs` — WNLA, circuits vs BP R1CS, range proofs vs BP, MACT.

Commands:

```sh
cargo test --release --features "bppp parallel yoloproofs"   # everything (100 tests)
cargo test --release --features yoloproofs                    # BP only, incl. golden
cargo test --release                                          # default features
python3 -I ref/gen_vectors.py && git diff --stat tests/vectors # must be empty
python3 -I ref/xcheck_secp256k1_zkp.py                        # 5/5 and 13/13
cargo bench --features "bppp yoloproofs" --bench bppp
```

## Method (used for every phase)

1. Write the spec section first, with exact layouts (column order, slots, row order) so that
   independent implementations build the same objects. Derive formulas yourself and check
   them numerically (a short Python script with random instances) before relying on them.
2. Have a **separate agent** write the Python reference for that section from the spec and the
   paper only (it must not read `src/bppp/` or other BP++ implementations), with self-checks
   and vectors in a pinned JSON format. Its report usually finds spec ambiguities; fix the spec
   rather than letting either side guess.
3. Implement in Rust with tests first (TDD); then a test that reproduces the reference vectors
   exactly; then mutation probes (mutate a copy of the repository outside the checkout, run the
   tests, make sure the important lines are caught).
4. A fresh reviewer on the most capable model reviews the phase against the spec, with a
   "Review Focus" list of the likeliest failure modes; fix Critical/Important findings with a
   failing test first; record deferred minors.
5. Commit per logical step; update this file's progress log and the errata.

## The owner's rules

- Talk in Ukrainian or English, the language of the question. **Never write in Russian.**
- Committing finished, tested work in this repository is fine without asking; **push and
  merge into `main` only when the owner asks.** End commit messages with the session's
  attribution lines.
- The reference implementation for BP++ is Blockstream's **secp256k1-zkp** (module `bppp`;
  open PRs #207 — reciprocal range proof, #352 — norm argument of arbitrary length). **Do not
  rely on distributed-lab/bp-pp** (the owner considers it unreliable).
- BP proof bytes never change (golden tests). Parallelism only behind the `parallel` feature,
  with identical results. Secret scalars only in constant-time code. Every challenge is drawn
  after everything it must bind (statement digest, generators G and H_0, inputs, commitments).
- Errors, never panics, on malformed input reachable through the public API. BP++ code returns
  only `ProofError::{InvalidGeneratorsLength, FormatError, VerificationError}`
  (`From<ProofError> for R1CSError` panics on the others).

## Next: phase 6 — `CircuitBuilder`

An additive trait (`ConstraintSystem` stays as is) implemented by both backends: BP emulates
the gadgets with logUp over its two-phase randomized constraints, BP++ builds a reciprocal form
circuit natively. A gadget is written once.

```rust
pub trait CircuitBuilder: ConstraintSystem {
    fn witness(&mut self, v: Option<Scalar>) -> Variable;                 // BP: allocate (half a gate); BP++: a slot in n_O, free
    fn product(&mut self, l: LinearCombination, r: LinearCombination, out: LinearCombination); // a row of W_m
    fn table(&mut self, rows: impl IntoIterator<Item = Vec<u64>>, widths: &[Width]) -> TableId;
    fn lookup(&mut self, t: TableId, tuple: &[LinearCombination]);        // BP: one phase-2 multiplier; BP++: one gate
    fn lookup_value(&mut self, t: TableId, v: Option<u64>) -> Variable;
    fn reciprocal(&mut self, widths: &[Width]) -> Reciprocal;             // add / sub / add_public
    fn finish_reciprocal(&mut self, r: Reciprocal) -> Result<(), R1CSError>;
}
pub trait VectorInputs { fn commit_vec(&mut self, v: &[Scalar], r: Scalar) -> (CompressedRistretto, Vec<Variable>); } // BP++ only
```

- Tuples are packed into one pole with a public base, so components must be range-bounded
  (sum of widths < 252 bits); a `Bounded<N>` type can enforce it.
- BP side ("6a", independent of BP++): port bpvm's `LogUp` gadget (`crates/bpvm-zk/src/logup.rs`
  in bpvm) into the fork as the BP implementation.
- Requirements from the phase-3 review:
  - a **two-phase prover** (typestate): `commit_initial(c, InitialWitness) -> (Pending, alpha)`
    then `Pending::finish(LateWitness { w_r, w_o_lr })`, or a closure
    `FnOnce(alpha, &w_P) -> LateWitness`, because ordinary rows that read reciprocals make `w_R`
    and the `LinR` slot depend on alpha (the current `reciprocal::prove` takes them up front);
  - every builder variable carries its phase; late variables are rejected in numerators,
    poles and randomized constraints at construction time;
  - dalek-style randomized constraints (shuffle etc.) must not be mapped to a challenge between
    `C_O` and `C_R`: a right-wire variable from `allocate()` is unbound there.
- Cost model (estimates to replace with measurements, against the fork's BP + logUp):
  range32 6 → 4 gates (byte table) or 2 (16-bit table); XOR32 24.5 → ≈5 with an (a, b, a⊕b)
  table of 2^16; memory/bus 1 → 1 per tuple; a bpvm CPU row 35.5 → ≈22 (byte tables) or ≈17.
- Tests: the same gadgets (range32 via a byte table, XOR via a table, a memory permutation, a
  MACT balance) proven on both backends; pin gate counts; a component wider than declared is
  an error.

## Then: phase 7 — performance and hardening

- WNLA prover: deferred folding of the generators (as `DEFERRED_ROUNDS` in
  `src/inner_product_proof.rs`), no copies in `split`; consider variable-time MSMs inside the
  circuit protocol (its WNLA inputs are uniformly random — secp256k1-zkp computes the norm
  argument in variable time; paper Theorem 2).
- Circuit prover: parallel `add_transposed`/flatten, streaming `l(τ)`, `n(τ)`; the R1CS
  translation copies the constraint store into a `SparseMatrix` (≈6× BP's memory on 4M
  constraints) — consume it row by row or keep interned coefficients.
- Rekey the BP++ prover's RNG with the circuit digest (and a witness hash), as defense in depth.
- Drop the empty `C_O` in shared-multiplicity proofs (paper; −32 B).
- Batch verification (paper §4.3, last paragraph).
- Golden vectors for BP++ proofs (fixed RNG) once the format is frozen; fuzzing of
  `from_bytes`; a test where the verifier sees a zero challenge with a proof crafted for it.
- Memory and time on 2^20 / 2^24 gates; a table BP vs BP++ (size, prove, verify, RSS).

## Then: phase 8 — bpvm on BP++ (repository github.com/juja256/bpvm)

Port the chips to `CircuitBuilder` (6a gives this for BP immediately), add
`bpvm prove --backend bp|bppp`, measure fib / sha256 / ec_mini / ec_add, update README and
DESIGN (milestone M6). bpvm depends on this fork by git revision.

## Deferred findings (from the reviews)

- Verifier-side test with a zero challenge needs a proof crafted for it.
- Witness zeroization (prover intermediates) — crate-wide policy.
- `is_satisfied` (test/diagnostic helper) is not constant time; document if exposed further.
- Performance nits: batch inversions in `reciprocal::compile`/`reciprocals`, the verifier
  re-running `check()`, `VecPoly::inner` computing both orders of pairs.

## Progress log

- 2026-10-19 — phases 1–5 done and reviewed (0 Critical in every review); errata 1–18.

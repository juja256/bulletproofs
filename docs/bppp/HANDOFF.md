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
| 6 | `CircuitBuilder` | `src/r1cs/builder.rs`, `backend.rs`, `prover.rs`, `verifier.rs`, `compact.rs`, spec §7 | branch `claude/beautiful-goodall-m369g7` (local commits, not pushed) |
| 7 | performance and hardening | — | open |
| 8 | bpvm on BP++ | other repository | open |

The branches are stacked: `main` ⊂ `bppp-circuit` ⊂ `bppp-reciprocal` ⊂ `bppp-range` ⊂
`bppp-r1cs` ⊂ `claude/beautiful-goodall-m369g7` (phase 6). None of 2–5 is merged into `main` yet; ask the owner before merging.

Numbers (Apple M4 Pro, one thread): a 64-bit range proof is 416 B (paper's figure) against 672 B
for the BP `RangeProof`, proving in 2.55 vs 4.39 ms, verifying in 0.48 vs 0.61 ms; a circuit of
2^14 multiplications 1056 B vs 1313 B, verify 52 vs 77 ms, prove 1.10 vs 0.99 s (prover not yet
optimised); the same circuit through the R1CS front end on BP++ 817 B at 2^10.

## Map of the repository

- `docs/bppp/spec.md` — the normative specification (§1 conventions, §2 WNLA, §3 circuits,
  §4 reciprocal form, §5 range/MACT, §6 R1CS). The paper's typeset formulas in §5 are wrong in
  several places; the spec re-derives them. Implementations follow the spec, not the paper.
- `docs/bppp/bppp-paper-errors.tex` — errata of the paper (19 items, each with location,
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
cargo test --release --features "bppp parallel yoloproofs"   # everything (≈150 tests)
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

## Done: phase 6 — `CircuitBuilder` (spec §7)

What exists:

- `CircuitBuilder: ConstraintSystem` (object safe), implemented by `Prover` and `Verifier`:
  `witness`, `product`, `table(rows: Vec<Vec<u64>>, widths)`, `lookup`, `lookup_value`,
  `reciprocal` → `Reciprocal { add, sub, add_weighted, add_public }`, `finish_reciprocal`, and
  `cost() -> Cost { bp_phase1, bp_phase2, bppp_gates, bppp_lin }` with
  `Cost::gens_capacity(backend)`. New `Variable::Witness(i)`.
- The builder only records; at prove/verify it is finalized (multiplicity witnesses, counted in
  constant time) and lowered to BP (logUp over randomized constraints, port of bpvm's `LogUp`,
  §7.5) or to a BP++ reciprocal form circuit (§7.6, proof tag 3). Same gadget code, any time
  `set_backend`. Gadgets that use only `ConstraintSystem` keep the §6 translation (tag 2).
- Tuples are packed with a public base; components of multi-column tuples need bounds recorded
  by one-column table lookups (§7.3), enforced on both backends so that gadgets are portable.
  The phase plan's "every variable carries its phase" became: builder operations exist only in
  phase 1 and their variables must exist at the call; numerators and coefficients that read
  `MultiplierRight` are copied into initial columns (§7.6).
- `reciprocal::prove_two_phase` (callback `(alpha, w_P) -> LateWitness`), spec §4.3; the builder
  itself needs only the one-phase prover (it exposes no reciprocals).
- Tests: `tests/builder.rs` (range32 via a byte table, nibble XOR table, memory permutation,
  MACT balance on both backends, costs and proof sizes pinned, copies, no gates, object safety,
  mode switching, missing variables, malformed proofs); `src/r1cs/vectors.rs` (41 reference
  cases); `src/r1cs/soundness.rs` (cheating provers via test-only hooks `builder::cheat`).
- Numbers (one gadget statement of `tests/builder.rs`): BP 282 + 41 multipliers (padded 512),
  BP++ 42 gates but `N_lin = 526` (witnesses and multiplicities beyond the norm slots).

Deferred from phase 6 (with the review's grading):

- The bound rule costs one extra lookup per unbounded component on BP as well (parity, A2);
  consider a BP-only relaxation or document amortization (bounds persist per variable).
- Multiplicity counting is `O(|T| |Q|)` (constant time); an oblivious sort would give
  `O((|T| + |Q|) log)`. Matters for 2^16-row tables (phase 7).
- Recorded LCs are `Vec<(Variable, Scalar)>` per lookup (≈150 B each); compact them (phase 7).
- Public rows are `u64` only (no field-element tables); `VectorInputs::commit_vec` of the
  sketch is not implemented (not needed by the gadgets so far).
- The prover does not refuse violated linear constraints (both backends, as upstream BP): it
  produces a proof that does not verify (M1).
- `prove_two_phase` takes a full witness with placeholder late entries rather than a typed
  `InitialWitness` (M3, documented).
- Errors are string `GadgetError`s.

## Next: phase 7 — performance and hardening

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
- Builder: oblivious-sort multiplicities, compact recorded LCs, `N_lin` growth (witnesses beyond
  the norm slots enlarge `H` and the verifier's MSM: consider putting witnesses into spare
  gates, or `LinL`), measured costs replacing the estimates of the old phase-6 plan
  (XOR32 ≈ 5 gates ignored both BP's `|T|/2` multiplicity multipliers and BP++'s `N_lin`).

## Then: phase 8 — bpvm on BP++ (repository github.com/juja256/bpvm)

Port the chips to `CircuitBuilder` (6a gives this for BP immediately), add
`bpvm prove --backend bp|bppp`, measure fib / sha256 / ec_mini / ec_add, update README and
DESIGN (milestone M6). bpvm depends on this fork by git revision.

## Deferred findings (from the reviews)

- Verifier-side test with a zero challenge needs a proof crafted for it.
- `ConstraintStore::push` still asserts (panics) beyond `2^29` variables.
- Witness zeroization (prover intermediates) — crate-wide policy.
- `is_satisfied` (test/diagnostic helper) is not constant time; document if exposed further.
- Performance nits: batch inversions in `reciprocal::compile`/`reciprocals`, the verifier
  re-running `check()`, `VecPoly::inner` computing both orders of pairs.

## Progress log

- 2026-10-19 — phases 1–5 done and reviewed (0 Critical in every review); errata 1–18.
- 2026-10-19 — phase 6 started. Checked green: 100 tests (bppp parallel yoloproofs), 52 BP-only,
  vectors regenerate unchanged, xcheck 13/13. Spec §7 (circuit builder) written: the builder
  records operations backend-independently (new `Variable::Witness`), finalizes tables into
  reciprocal arguments, and lowers to BP (logUp port, §7.5) or to a reciprocal form circuit
  (§7.6). Tuples are packed with a public base; components of multi-column tuples must have a
  bound recorded by a one-column table lookup (§7.3, checked on both backends). §4.3 gains the
  two-phase prover (callback for late values); the builder itself needs only the one-phase one.
  Independent Python reference for §7 started (agent, spec/errata/paper/ref only). The paper PDF
  is not reachable from the container (eprint blocked); the owner uploaded it, text extracted to
  the session scratchpad (not committed).
- 2026-10-19 — phase 6 implementation: two-phase reciprocal prover (`reciprocal::prove_two_phase`,
  `LateWitness`); `CircuitBuilder` (`src/r1cs/builder.rs`) with the BP lowering (6a, logUp port)
  and the BP++ lowering (`backend::builder_circuit`, proof tag 3); gadget tests on both backends
  in `tests/builder.rs` (range32 via a byte table, nibble XOR table, memory permutation, MACT
  balance; costs pinned: BP 282 + 41 multipliers, BP++ 42 gates). Independent reference: 41
  cases in `builder.json` (13 proven, 3 unsatisfied, 2 prover errors, 23 construction errors);
  `src/r1cs/vectors.rs` reproduces all of them (circuit, witness, costs, commitments, real proofs
  on both backends) on the first run. The reference's 13 ambiguity notes are pinned in §7; its
  interpretations matched the Rust code in every case.
- 2026-10-19 — phase 6 hardening: cheating-prover tests (`src/r1cs/soundness.rs`, test-only
  hooks in `builder::cheat`: forged multiplicities, a tuple colliding without BP's compression
  challenge, forged denominator and numerator); errata remark on lookups of tuples; benchmark
  `builder_bench`. Mutation probes: 32 mutants of builder, lowering, flatten, two-phase prover;
  28 killed by the first run, the 4 survivors got tests (2 were the cheats above, written after
  the snapshot; 2 new tests). Review on the most capable model started.
- 2026-10-19 — phase 6 review (most capable model): 0 Critical, 2 Important, 6 Minor, 3 API notes.
  Fixed with failing tests first: I1 multiplicities counted in constant time; I2 constraints on
  missing variables are a `GadgetError` in BP too (it panicked serially and silently dropped the
  term with `parallel`); M2 builder mode only after a successful operation; M5 zeroization on
  the error path; A1 `Cost::bppp_lin`, `Cost::gens_capacity`; A3 object-safe trait. Deferred:
  see "Deferred from phase 6". Re-run mutants: all 32 killed. Benchmark `builder` (README):
  1024 × range32, BP++ 945 B / 1.13 s / 75 ms vs BP 1345 B / 1.26 s / 119 ms. Everything
  green: 124 tests (bppp parallel yoloproofs), 67 (yoloproofs, golden unchanged), 34 (default);
  vectors regenerate unchanged; xcheck 5/5, 13/13. Not pushed.
- 2026-10-19 — phase 7 started on branch `bppp-perf` (from `bppp-builder`). Owner's decisions:
  variable-time MSMs inside the circuit protocol behind a feature, constant time by default;
  format changes allowed (drop the empty `C_O`, builder witnesses beyond the norm slots).
  Safety net: `tests/bppp_regression.rs` pins the SHA3 of BP++ proofs (fixed RNG, all front
  ends; same with `parallel`). Profiler `examples/bppp_profile.rs`. Baseline on this machine
  (Xeon 2.1 GHz, one thread): circuit 2^14 prove 2.53 s (WNLA 1.47 s, the four CT
  commitments 1.06 s), verify 134 ms; 2^16: prove 10.7 s, 123 MB; R1CS on BP++ 2^16 11.3 s,
  149 MB vs BP 10.1 s, 94 MB. Micro: CT MSM 16 µs/term, VT MSM 5 µs/term, a 2-point fold
  48 µs, `P + sQ` 38 µs. The CT prover is all MSMs: commitments 4 N terms, WNLA ≈ 3 N terms
  plus N folds of the norm generators.
- 2026-10-19 — WNLA prover: single MSMs for X and R without copies, deferred folding (2 rounds
  CT, 3 VT), one scalar multiplication per fold; proofs unchanged. Feature `bppp-vartime`
  (owner's choice: CT by default). Circuit 2^14: prove 2.70 → 1.72 s with `bppp-vartime`
  (CT: WNLA −7%); peak memory −20%. Dropping `C_O`: the paper's ZK proof does not cover it
  (errata 19); a rank computation (`ref/checks/drop_co_zk_rank.py`) says it is still HVZK.
  The owner asked to discuss the builder's proof format and API (`BuilderProof`,
  `CircuitBuilder` vs `ConstraintSystem`, integration with bpvm) after this phase, so the
  format changes (drop `C_O`, builder overflow layout) wait for that discussion.
- 2026-10-19 — phase 7, continued: oblivious (bitonic) multiplicity counting for large tables
  (2^16 rows × 2^12 lookups 0.8 s instead of 13 s, constant time); prover RNG keyed with the
  digest and the (initial) witness (regression pins updated); `BatchVerifier` (spec §3.11);
  fuzz-style malformed-proof tests; zero lambda/gamma completeness. Large measurements in the
  README: at 2^20 BP++ proves in 171 s (129 s vt) vs BP 176 s, verifies in 11.5 vs 15.7 s,
  1457 vs 1697 B, but needs 1.82 vs 1.24 GB. `docs/bppp/builder-api-notes.md` prepares the
  owner's API/format discussion.
- 2026-10-19 — phase 7 review (most capable model): 0 Critical, 1 Important, 7 Minor. Fixed:
  I1 the prover RNG is now derived from the live transcript after the statement (as BP's
  `TranscriptRng`), then rekeyed with protocol, digest and witness hash — before, the same
  witness in two contexts reused blindings under a weak RNG (test first; pins updated); M1
  errata 19 and its script (shared discrete logs, special challenges, caveats); M2 debug
  assertion in the oblivious sort; M3 empty batch verifies without generators, RNG documented;
  M4 doc references; M5 witness hash zeroed with `Clear`; M6 VT chunk size, a deferred vector
  that stops folding is materialised at once. Not done: M7 (cosmetic duplication). Mutants of
  phase 7: 19 of 20 killed, the survivor (materialising one round later) is equivalent.
  Tests: 139 (bppp parallel yoloproofs, also bppp-vartime), 70 (yoloproofs, golden unchanged),
  34 (default). Phase 7 done except the format changes held for the owner's discussion.

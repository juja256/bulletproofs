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
| 7 | performance and hardening | `wnla.rs`, `batch.rs`, `oblivious.rs`, spec §2.6, §3.11 | branch `bppp-perf` (pushed); format changes held |
| 7b | tuple poles (option F): lookups of tuples without the bound rule | `reciprocal.rs`, `builder.rs`, `backend.rs`, spec §4.1–4.7, §7.2–7.6 | branch `bppp-tuples` (pushed); reviewed, done |
| 7c | option B: one BP++ lowering and encoding for every constraint system | `prover.rs`, `verifier.rs`, `proof.rs`, `backend.rs`, spec §6, §7.7 | branch `bppp-one-proof` (pushed); reviewed, done |
| 8 | bpvm on BP++ | bpvm `main`; here `R1CSProof::backend`, feature `cheats`, prover and verifier speed-ups | done, reviewed |

All phases are merged into `main` (2026-10-20, fast-forward to `f9f540a`, pushed); the
`bppp-*` branches are kept for history.

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
  (Superseded by option B, phase 7c: one BP++ lowering for every constraint system, tag 4.)
- Tuples are packed with a public base; components of multi-column tuples need bounds recorded
  by one-column table lookups (§7.3), enforced on both backends so that gadgets are portable.
  (Superseded by option F, phase 7b: tuple poles compressed with eta, no bound rule.)
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
- 2026-10-19 — phase 7b (option F, owner's decision after the API discussion: bpvm relies on
  lookups bounding tuple components) started on branch `bppp-tuples` (from `bppp-perf`, which
  is pushed). Spec first: §4.1 tuple poles $w_{D,i} = \sum_j \eta^j x_{i,j}$ over early columns
  ($C_O$), public poles as polynomials in $\eta$; §4.3 protocol v2 $C_O, \eta, C_L, \alpha, C_R$
  only for circuits that use $\eta$ (v1 unchanged: range, MACT, all existing vectors); §4.4/4.5
  digest and transcript v2; §4.7 soundness argument (Schwartz–Zippel over $\eta$, rows must
  not mix free and tuple poles); §7.2/7.3 widths and the bound rule removed (`table(rows)`,
  `reciprocal(m)`), §7.6 tuple poles for $m \ge 2$ with copies of components that read $w_L$,
  $w_R$. The challenge is called $\eta$ (label `"eta"`): $\gamma$ is taken by the WNLA rounds.
  Errata remark "Lookups of tuples" updated.
- 2026-10-19 — phase 7b, implementation. Owner's answers to the API notes: A (keep the builder
  on `Prover`/`Verifier`), B by our choice (one BP++ encoding, after F), not C. Rust: `Pole`
  (polynomial in $\eta$), `TuplePole`/`Component`, `uses_eta`, protocol v2 in
  `reciprocal.rs` (`commit_ol` split into `commit_o`/`commit_l`, same randomness order);
  builder `table(rows)`, `reciprocal(m)`, tuple poles for $m \ge 2$ with copies of components on
  $w_L$/$w_R$; bound rule, widths and the 512-bit bound arithmetic removed. Tests: tuple cheats
  (packed collisions with unbounded components, swapped tuples, component order), rules for tuple
  poles, v2 digest and transcript order, v2 in a batch, bpvm-style `xor32` with fresh nibbles
  (8 gates). Independent reference (separate agent, spec and `ref/` only): 10 new reciprocal
  cases and 12 new builder cases, digests v1/v2 for every case, all 13 one-column builder cases
  unchanged; Rust matched on the first run. One spec ambiguity found (§7.6 vs §4.1 for an
  $m \ge 2$ argument with only empty public coefficients): §7.6 now defers to §4.1. Everything
  green: 145 tests (bppp parallel yoloproofs, also bppp-vartime), 70 (yoloproofs), 34 (default);
  pins and range/MACT/circuit/WNLA vectors unchanged; xcheck 13/13. Next: mutants, review, then B.
- 2026-10-19 — phase 7b review (most capable model): 0 Critical, 0 Important, 5 Minor. Fixed:
  M1 a reciprocal row with a tuple pole or a long pole ("$\eta$-row") must not read a free pole's
  reciprocal (a free pole is committed after $\eta$ and could cancel any tuple) — now a rule of
  §4.1 checked by `check()`, the reference rejects it too and `reciprocal.json` has 9
  shape-invalid cases (`shape_ok: false`); M2 §4.7 says numerators may follow $\eta$; M3 the rekey
  copy of $w_D$ is zeroized with `Clear` (the `at_eta` copy falls under the crate-wide
  zeroization item); M4 the reviewer's probes kept as `src/bppp/tuple_tests.rs` (numerators and
  rows reading tuple poles, two-phase prover with tuple poles, v2 from long public poles alone,
  malformed v2 circuits); M5 §4.7 states the special-soundness assumption. Not done: a cheating
  prover for a wrong copy on BP++ (an ordinary §3 linear row; the BP++ prover refuses
  unsatisfied circuits anyway), caching `uses_eta`. Mutants of phase 7b: 20 of 20 killed.
  Tests: 149 (bppp parallel yoloproofs, also bppp-vartime), 70 (yoloproofs), 34 (default);
  vectors regenerate unchanged; xcheck 13/13. Phase 7b done.
- 2026-10-19 — phase 7c (option B, owner: "one proof") started on branch `bppp-one-proof` (from
  `bppp-tuples`). Spec first: §6.1 every constraint system on BP++ is lowered by §7.6 (a plain
  R1CS is the case $N_p = 0$, the same circuit as the old §6 translation); §6.2 one protocol (§4,
  `"bppp-r1cs v2"`) and one encoding (byte 2, $N'_m$, $N_{lin}$; tag 3 gone); §7.2 no builder mode;
  §7.7 points to §6.2. Changes the BP++ proofs of plain constraint systems (pins).
- 2026-10-19 — phase 7c, implementation and review. `prove_bppp`/`verify_bppp` lower every
  constraint system with `builder_circuit` and prove it with `reciprocal::prove` under
  `"bppp-r1cs v2"`; the §6 translation (`backend::circuit`, `Constants`) and `BuilderProof` are
  removed; `builder.active` is left for BP only. Independent reference: plain programs lowered by
  §7.6 and checked against a direct §6.1 construction (150 random programs), 4 new builder
  cases, among them a violated linear constraint whose prover circuit differs (`prover_a_l`,
  `prover_digest`). Review (most capable model): 0 Critical, 2 Important, Minor. Fixed: I1 the
  tag is now 4 (an old tag-2 proof of a plain R1CS had the same header and body layout and would
  only fail verification; now a format error); I2 the vector test picks the protocol's
  challenge order (v2 with eta) for prover-circuit cases; I3 tests for the empty constraint
  system, a `Witness` in a plain constraint, old tags; Minor: HANDOFF "Done: phase 6" notes the
  superseded parts, the reference's `builder_mode` renamed. Not done: `proof_from_bytes_shape`
  builds a dummy circuit (pre-existing, cosmetic); `finish_reciprocal` of an empty argument
  sets `active` (harmless). Mutants of 7c: 8 of 8 killed. Pins of the R1CS front end updated
  twice (protocol, then tag). Tests: 151 (bppp parallel yoloproofs, also bppp-vartime), 70
  (yoloproofs), 34 (default); vectors regenerate unchanged; xcheck 13/13. Phase 7c done.
- 2026-10-19 — the cloud work (phases 6–7c) accepted on the owner's machine (Apple M4 Pro):
  151 tests (bppp parallel yoloproofs, also bppp-vartime), 70 (yoloproofs), 34 (default);
  vectors regenerate unchanged; xcheck 5/5, 13/13.
- 2026-10-19 — phase 8 started. Here, branch `bppp-bpvm` (from `bppp-one-proof`):
  `R1CSProof::backend()` (bpvm's verifier takes the backend from the proof) and the testing
  feature `cheats` (`r1cs::cheats::set_unchecked_prover`, thread-local): the prover counts
  multiplicities only for lookups that equal a row and the BP++ prover proves unsatisfied
  circuits (`reciprocal::prove_unsatisfied`, same derived randomness), so that downstream
  crates can test that the verifier rejects cheating proofs; honest proofs unchanged (pins).
  Tests `tests/cheats.rs`; 155 with `cheats`. bpvm (branch `bppp`, by path dependency until
  this branch is pushed): `Env` on `CircuitBuilder` (tables, lookups, reciprocal arguments for
  memory and bus; one-column range tables per digit width; free witnesses), `prove(st, wit,
  backend)`, `bpvm --backend bp|bppp`; all VM tests and five tampered traces on both backends.
  fib: BP 4424 multipliers, 1345 B, verify 40 ms; BP++ 2450 gates + 1683 linear, 945 B, 26 ms.
- 2026-10-19 — phase 8 review (most capable model): 0 Critical, 1 Important (no bpvm test
  caught a dropped fetch lookup), Minor (gadget tests that did not exercise the range lookup,
  shape-only circuit binding, CLI verify checks, unbounded steps, proof-file version). Fixed in
  bpvm with mutation probes (dropped fetch, all digits from the 8-bit table: both killed).
  Profiling bpvm on BP++ with `parallel` (macOS `sample`) found sequential prover work:
  `reciprocals` inverted every denominator separately (17% of a sha256 proof) — now one batch
  inversion; `VecPoly::inner` (14%) — weights folded once, symmetry of `p.inner(p)`, parallel
  inner products, one weighted term alive at a time. Proofs identical (pins). sha256 on BP++
  with `parallel`: prove 6.2 → 4.1 s (BP 4.8 s); ec_add ($2^{24}$): 240 → 159 s (BP 166 s).
  Remaining sequential work, mostly in the verifier: `ReciprocalCircuit::check` compiles the
  circuit a second time with dummy coefficients, `compile`/`add_transposed`/`eval`,
  `Weights::new`, the circuit digest, the oblivious sort of multiplicities; at $2^{24}$ the BP++
  verifier takes 32 s against BP's 16 s with `parallel` (single-threaded BP++ verifies faster).
  BP++ prover memory: ec_mini 2.14 GB vs BP 1.13 GB, ec_add 8.5 vs 10.1 GB. Tests: 156
  (bppp parallel yoloproofs cheats), 152 (bppp yoloproofs), 70, 34.
- 2026-10-20 — refactoring review (owner's request: smaller, clearer code and API names; two
  fresh reviewers: BP++ core, R1CS/builder/bpvm). Done, proofs and vectors unchanged in every
  step (pins, golden, reference vectors): one prover path with the randomness as a closure
  (`Randomness`/`DynRng` gone, digest computed once); `bppp::terms::Terms` for circuits, batch
  and WNLA; `BpppGens::capacity`/`check_dims`, `H_FIXED`, `{Arithmetic,Reciprocal}Circuit::gens`;
  `CircuitProof::from_bytes_dims` (no dummy circuits); named blinding masks; Range/MACT
  `setup()`; `Builder.active` removed; one backend `match` in verify. API: **`Reciprocal` is a
  handle recorded at creation** (a forgotten `finish_reciprocal` used to drop the argument
  silently; spec §7.2/§7.4 updated), `constrain_product`, `Cost::{gates, linear}`,
  `bppp_linear`, `Backend: Display + FromStr`, `cheats::with_unchecked_prover`,
  `CircuitProof::prove`, `WnlaProof::prove`, `ReciprocalProof`, crate-private protocol
  modules, `WnlaStatement.{h, n}`. Tests of circuit/reciprocal in their own files. README:
  "Writing gadgets for both backends" (example `tests/guide.rs`). bpvm follows (`Env::mem_read`
  etc., `witness`, `Stats.gates`). Not done (judged not worth the churn or needing review):
  shared layout for `cost()` and the BP++ lowering, splitting `backend.rs`/`builder.rs` and the
  BP body of `prover.rs`, one evaluator for prover and lowering (cfg mismatch), matrix field
  renames `w_l` → `W_l` (collides with the witness names), moving `builder::cheat` into
  `cheats.rs`, merging overlapping integration tests, `msm_*` chunk parameter, the verifier's
  second compilation in `ReciprocalCircuit::check` (performance), panics of `SparseMatrix` on
  reachable input. Tests: 162 (bppp parallel yoloproofs cheats), 157, 74, 34.
- 2026-10-20 — BP++ verifier parallelised (owner: the multi-threaded BP++ verifier was slower
  than BP's). Profiling (macOS `sample`) and fixes, proofs unchanged: `ReciprocalCircuit::check`
  checks the compiled shape from the dimensions (`circuit::Shape`, shared with
  `ArithmeticCircuit::check`) instead of compiling a second time — test
  `shape_check_agrees_with_compiling` against the old definition (`check_by_compiling`) on
  every vector case and boundary mutations; pole factors by one batch inversion; parallel
  `add_transposed` (column ranges, no extra memory), `VecPoly::eval`, weights, tuple rows of
  `compile` and the R1CS lowering (chunks in bounded waves, `util::map_in_order`);
  `BufHasher` for digests; `sha3` feature `asm` (ARMv8 SHA3 instructions, runtime
  detection). Review (most capable model): 0 Critical, 0 Important; minors fixed (version floors
  sha3 0.10.7 / keccak 0.1.6, stronger shape test, debug assertions). bpvm with `parallel`:
  verify sha256 0.71 → 0.39 s (BP 0.43), ec_mini 2.20 → 1.15 s (BP 1.06), ec_add 32.0 → 15.6 s
  (BP 16.4); prove ec_add 159 → 132 s (BP 166). Heap peaks unchanged (`mem_profile`). The
  remaining sequential part is the circuit digest (SHA3, before any challenge; parallel tree
  hashing would change the format). Tests: 165, 160, 74, 34.
- 2026-10-20 — merged into `main` (fast-forward, 64 commits) and pushed, on the owner's word;
  bpvm depends on `rev = f9f540a` and is pushed too (bpvm `main` `c5f9cd4`).


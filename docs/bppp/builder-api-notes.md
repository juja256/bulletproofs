# Circuit builder: API and proof-format decisions (for discussion)

Written at the end of phase 7, before the discussion the owner asked for (answers in §4): why the builder
(phase 6) looks as it does, what it costs, and the alternatives, with an eye on bpvm (phase 8).
Nothing here is settled; the format changes of phase 7 that touch the builder were held back
for this discussion.

## 1. What was decided, and why

### 1.1 `CircuitBuilder: ConstraintSystem`, implemented by `Prover` and `Verifier`

*(2026-10-22: superseded by the API refactor: one trait `ConstraintSystem` with the builder
operations, randomized constraints internal, `metrics` gone.)*

- **Why a supertrait.** Gadgets mix plain R1CS operations (`multiply`, `constrain`, `allocate`)
  with builder operations (`lookup`, `reciprocal`) on the same variables. With one trait object
  per side, a gadget has one `cs` and existing gadgets keep working unchanged.
- **Why on `Prover`/`Verifier`.** The phase-6 plan said "an additive trait implemented by both
  backends"; the backends are selected on `Prover`/`Verifier` by `set_backend` (phase 5), so the
  builder lives there too, and one proof type (`R1CSProof`) covers all cases.
- **Cost.** `Prover`/`Verifier` now carry two very different things: the R1CS front end and a
  builder record. The trait is object safe (after the review), but `ConstraintSystem` brings
  BP-isms with it (`allocate` half-multipliers, `RandomizableConstraintSystem` that BP++ refuses).

### 1.2 Record now, lower at `prove`/`verify`; `Variable::Witness`

- The builder records operations backend-independently and lowers them only at prove/verify
  (finalization of tables needs all lookups first anyway). So `set_backend` may be called at
  any time, and prover and verifier lower the same record.
- `witness()` must return a variable before the backend is known, hence the new
  `Variable::Witness(i)`: half a multiplier in BP (paired at lowering), a free `w_O` slot in
  BP++. **Cost:** a new variant of a public enum (breaks exhaustive matches downstream), and a
  witness-to-wire mapping inside BP's `flatten`.

### 1.3 Builder mode and the proof tag 3 (`BuilderProof`) — superseded by option B

(Option B, phase 7c: every constraint system is lowered by §7.6 and proven with §4 under
`"bppp-r1cs v2"`; one encoding, tag 4 with `(N'_m, N_lin)`; no builder mode. The text below is
the phase-6 design.)


- A constraint system that uses builder operations is lowered to a **reciprocal form circuit**
  (§7.6), one that does not to the **arithmetic circuit** of §6. These are different statements
  with different transcripts (`"bppp-builder v1"` vs `"bppp-r1cs v1"`), different digests and a
  different protocol (C_L, C_O, alpha, C_R vs C_L, C_R, C_O). §6 was kept byte-for-byte so that
  phase-5 proofs and tests do not change.
- `R1CSProof::from_bytes` parses without the circuit, so the encoding carries what the WNLA
  parser needs: §6 tag 2 carries `(N_m, k)`, the builder tag 3 carries `(N'_m, N_lin)` (`N_lin` is
  not a function of `k` in the builder layout). Hence a second tag rather than reusing tag 2.
- **Cost:** two BP++ encodings behind one type; "builder mode" switches on implicitly with the
  first successful builder operation, which is a subtle rule.

### 1.4 The bound rule (§7.3)

Tuples are packed with a public base (the phase-6 plan), so every component of a multi-column
tuple needs a bound recorded by a one-column lookup; enforced on both backends so that a gadget
accepted by BP is accepted by BP++. BP itself would not need it (it compresses with challenges).

## 2. Alternatives

| | option | pro | contra |
|---|---|---|---|
| A | keep as is | works, tested on both backends, small diff for gadgets | the points of §1 |
| B | one BP++ lowering for everything: §6 becomes the special case `N_p = 0` of §7.6 (one tag) | one encoding, no "builder mode" | changes phase-5 proofs (format not frozen anyway) |
| C | no dimensions in the encoding: `R1CSProof::from_bytes` keeps raw bytes, the verifier parses with its own dimensions | smaller, no per-kind tags beyond the backend | parse errors move to `verify` |
| D | a separate `CircuitBuilder` type (not `Prover`/`Verifier`) that produces a circuit + witness, then `bppp::prove`/`bp::prove` | clean separation, no BP-isms in BP++ gadgets, no implicit mode | gadgets written against `ConstraintSystem` need an adapter; two front ends to maintain |
| E | bound rule relaxed on BP (or only checked by an explicit `strict` mode) | no extra lookups on BP | a gadget can work on BP and fail on BP++ |
| F | tuple compression with a challenge in BP++ (extra commitment round: C_O, gamma, C_L, alpha, C_R) | no bound rule at all, lookups bound their components as in logUp | protocol change (spec §4, vectors, review), one more challenge |

## 3. bpvm (phase 8)

- bpvm's chips use `RandomizableConstraintSystem` and their own `LogUp`/`Lookup` over randomized
  constraints; BP++ refuses randomized constraints, so porting means replacing `Env`'s lookups
  and arguments by `table`/`lookup`/`reciprocal` (6a gives the same gadgets on BP).
- The bus tuple has 8 components (op, clk, pc, next_pc, imm, v1, v2, vd): about 224 bits, within
  252, but every component needs a recorded bound; LCs such as `pc + 4` are fine (non-negative
  small coefficients), differences such as `next_pc - pc` are not. Registers range-checked once
  amortise this; fresh per-row values pay one lookup each. Option F would remove the issue.
- Witnesses beyond the norm slots become linear slots (`N_lin`): for lookup-heavy circuits (many
  multiplicities) this enlarges `H` and the verifier's multiplication; the held-back layout
  change would halve it.
- Memory: BP++ proving uses about 1.6x BP's memory (R1CS front end, 2^16); fine at 2^20 on a
  workstation, worth a streaming prover later.

### 3.1 What bpvm relies on today (found when checking the bound rule against its gadgets)

bpvm has **no separate range checks** for the components of its multi-column lookups: logUp
compresses a tuple with challenges, so a lookup proves the tuple *is* a table row and thereby
bounds every component. `gadgets.rs` relies on it: `range_bits` queries `(d, k)` with a fresh
digit `d` in the two-column range table; `bitop` queries `(tag, na, nb, nr)` with three fresh
nibbles. Under the bound rule both queries are rejected. Porting: `range_bits` becomes one
one-column table per width (free); `bitop` needs a nibble lookup for each of the three nibbles
first (32 lookups per 32-bit operation instead of 8); bus and memory tuples pay one lookup per
component without a recorded bound. The rule therefore costs bpvm a real part of BP++'s gain,
which makes option F (challenge compression in BP++: C_O, gamma, C_L, alpha, C_R; same proof
size; components in C_L copied into C_O slots) the stronger candidate.

## 4. Questions for the owner — and the answers (2026-10-19)

1. Builder on `Prover`/`Verifier` (A) or a separate builder type (D)? **A** (bpvm keeps its
   arithmetic gadgets; only its lookup layer moves to `table`/`lookup`/`reciprocal`).
2. One BP++ encoding (B) and/or no dimensions in the encoding (C)? Left to us, the owner prefers
   one proof: **B** (after F: §6 becomes the case `N_p = 0` of §7.6, one tag, no implicit builder
   mode); **not C** (dimensions in the header let `from_bytes` reject malformed proofs early,
   16 bytes).
3. Bound rule: keep, relax on BP (E), or change the protocol (F)? **F**, implemented in phase 7b
   (spec §4.1–4.7, §7.3): tuple poles compressed with a challenge `eta` after `C_O`; the bound
   rule and the widths are gone (`table(rows)`, `reciprocal(m)`); bpvm's `bitop` costs 8 lookups
   per 32-bit operation again (test `xor32_with_unbounded_nibbles`).
4. Then: drop the empty `C_O` (errata 19 says it stays HVZK) and the builder overflow layout?
   Open. Both are compatible with F if done after it: a circuit that uses `eta` always has a
   non-empty `C_O` (the tuple components), so dropping an empty `C_O` touches v1 circuits only;
   an overflow layout may move witnesses into `C_L` only if they are not tuple components
   (multiplicities and numerators may move, components must stay in `C_O`).

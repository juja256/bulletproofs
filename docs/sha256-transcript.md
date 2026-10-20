# The SHA-256 transcript

`Sha256Transcript` (feature `sha256-transcript`, on with `secp256k1`) is a Fiat–Shamir transcript
built on SHA-256 alone. Every protocol of the crate takes it in place of `merlin::Transcript`. It
exists for verifiers that have SHA-256 but no Keccak, so no Merlin; the motivating one is a
Simplicity program on Liquid, which recomputes the challenges with the `sha_256_ctx_8_*` jets and
the secp256k1 scalar jets.

This document fixes the byte format. The reference implementation is
[`ref/sha256_transcript.py`](../ref/sha256_transcript.py) (hashlib only); the Rust code is
[`src/transcript/sha256.rs`](../src/transcript/sha256.rs).

## Format

The state is a single running SHA-256 context `ctx`. Integers are little-endian: `le32` (4 bytes)
and `le64` (8 bytes); `‖` is concatenation.

| operation | bytes written to `ctx` | output |
|---|---|---|
| `new(label)` | `t ‖ t`, where `t = SHA256("bulletproofs/transcript/sha256/v1")`; then `append_message("dom-sep", label)` | — |
| `append_message(label, msg)` | `0x41 ‖ le32(len(label)) ‖ label ‖ le32(len(msg)) ‖ msg` | — |
| `append_u64(label, x)` | `append_message(label, le64(x))` | — |
| `challenge_bytes(label, ℓ)`, `1 ≤ ℓ ≤ 2048` | `0x43 ‖ le32(len(label)) ‖ label ‖ le32(ℓ)` | the first `ℓ` bytes of `o_0 ‖ o_1 ‖ …`, where `o_i = SHA256-finalize(copy(ctx) ‖ le64(i))` |
| prover RNG (`build_rng`) | nothing | Merlin's RNG keyed with `SHA256-finalize(copy(ctx) ‖ 0x52)`; never used by a verifier |

A challenge leaves the copies behind: `ctx` keeps only the request record, so two challenges in a
row with no message between them still differ.

The tag `t ‖ t` fills exactly one block, so a verifier starts from a constant midstate instead of
hashing it:

```
init block (64 bytes): 3416d5f3e2e6bdf59de06c8882fd0942a9a4b2fcb081bb7a67003413526f065b
                       3416d5f3e2e6bdf59de06c8882fd0942a9a4b2fcb081bb7a67003413526f065b
midstate (8 words):    105e78ab 11f5800c cda67e37 ad7ec029 a3e22955 9300481a 30eedccc 9cb53d04
```

The KAT file [`tests/vectors/transcript/sha256.json`](../tests/vectors/transcript/sha256.json)
records the init block (`init_block`), the midstate after it (`midstate`, eight 32-bit words as
the SHA-256 state, after 64 bytes) and `R = 2^256 mod n` for secp256k1 (`r_secp256k1`).

## Scalars

A scalar challenge is `from_wide` of 64 challenge bytes `o_0 ‖ o_1` (two finalizations):

- **secp256k1:** `c = (o_0 ‖ o_1 read as a big-endian 512-bit integer) mod n`. Without a wide
  reduction: `c = normalize(o_0) · R + normalize(o_1) mod n`, with `R = 2^256 mod n`
  (`0x14551231950b75fc4402da1732fc9bebf`) and `normalize` the reduction of a 256-bit integer
  modulo `n` (Simplicity's `scalar_normalize`). Three scalar jets per challenge.
- **ristretto255:** `c = (o_0 ‖ o_1 read as a little-endian 512-bit integer) mod ℓ`
  (`Scalar::from_bytes_mod_order_wide`).

The 64 bytes keep every challenge uniform on any field; 32 bytes would be enough for secp256k1
(bias `2^-128`) but not for ristretto255.

## Why the encoding is unambiguous

Every input to SHA-256 has the form `t ‖ t ‖ R_1 ‖ … ‖ R_k ‖ s`:

- every record `R_j` starts with `0x41` or `0x43` and then states its own lengths;
- the suffix `s` is a challenge counter `le64(i)` with `i < 64` (its first byte is below `0x41`)
  or the RNG byte `0x52`.

So the sequence of operations is recoverable from the input. Different transcripts hash
different inputs, and SHA-256 can be modeled as a random oracle on them. No output is ever
extended, since each one finalizes a copy, so length extension does not apply.

## Cost in Simplicity

Each protocol absorbs records of fixed sizes: constant labels, 33-byte secp256k1 points, 32-byte
scalars, 8-byte integers. A verifier therefore writes them with `sha_256_ctx_8_add_N` for known
`N`. Per scalar challenge it pays two finalizations and three scalar jets. Per proof this is a
few compressions per round, negligible next to the multi-scalar multiplication (see the
verifier-cost notes of the owner's research).

## Vectors

- [`tests/vectors/transcript/sha256.json`](../tests/vectors/transcript/sha256.json): KATs from
  the reference (block boundaries, challenge lengths, back-to-back challenges, scalars on both
  curves), replayed by [`tests/transcript.rs`](../tests/transcript.rs).
- `tests/vectors/transcript/secp256k1-*.json`: full secp256k1 proofs under the SHA-256 transcript
  with the trace of every message and challenge; `python3 -I ref/sha256_transcript.py
  --check-trace tests/vectors/transcript/secp256k1-*.json` recomputes every challenge.
  The trace starts after `new(label)`: the record `append_message("dom-sep", label)` that
  `new` absorbs (with `label` = the file's `label`) is not in it. A verifier replaying a trace
  starts from the midstate, absorbs that record first, then the trace.

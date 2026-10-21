# Changelog

Entries are listed in reverse chronological order.

## Unreleased (this fork)

* Transcripts: every protocol takes its Fiat–Shamir transcript as `&mut T` for any
  `T: TranscriptBackend`; `merlin::Transcript` stays the default with byte-identical proofs.
  New `Sha256Transcript` (feature `sha256-transcript`, on with `secp256k1`): a transcript on
  SHA-256 alone, for verifiers without Keccak such as Simplicity
  (`docs/sha256-transcript.md`). Source changes for users:
  * the R1CS `Prover` and `Verifier` take `T: TranscriptRef` instead of
    `T: BorrowMut<merlin::Transcript>`: a `merlin::Transcript`, a `Sha256Transcript` or a
    `&mut` of any `TranscriptBackend` (code generic over `BorrowMut<Transcript>`, or passing a
    `Box<Transcript>`, needs updating);
  * `ConstraintSystem::transcript()` returns `&mut dyn TranscriptBackend`; calling its methods
    needs `use bulletproofs::TranscriptBackend;`;
  * the BP range-proof provers and the MPC dealer require `Clone` of the transcript.
* Simplicity verifier (feature `simplicity`, experimental; `docs/simplicity-verifier.md`):
  `Verifier::compile_to_simplicity` writes a Simplicity program that verifies BP++ R1CS proofs
  over secp256k1 with the SHA-256 transcript. Stage 3: IR passes (products of squares, balanced
  sums, CSE, DCE), values recomputed where read when cheaper than storing them, the final
  multiscalar multiplication as a balanced tree; new `Stats.stored` and `Report.data_mwu`, and
  `Stats.jets` counts executions.
* Earlier fork changes (Bulletproofs++, the circuit builder, the secp256k1 curve, Elements
  commitments) are described in the README.

## 5.0.1

* Support for `serde_json`. Any library trying to deserialize RangeProof from json would run into an error, which is now fixed.

## 5.0.0

* Change `curve25519-dalek-ng` dependency to `curve25519-dalek`. A major version bump is required because one cannot import `curve25519-dalek` and `bulletproofs` without conflicts.

## 4.0.0

* Update to `rand_core` `0.6`.  This requires a major version bump but the API
  is otherwise unchanged from the `3.x` series.

## 3.0.1

* Update repository URL.

## 3.0.0

* Add support for stable Rust.
* Update `curve25519-dalek` and internal dependencies.
* Tweaks to the (unstable) R1CS API.

## 2.0.0

* Switch from `failure` to `std`-compatible errors via `thiserror`.
* Update `rand`, `curve25519-dalek`, `merlin` versions.
* Adds `no_std` support by @xoloki.

## 1.0.4

* Change doc-include paths to allow compilation on the latest Rust nightly
  (which changed the path root).
* Various changes to the (unreleased, unstable) R1CS implementation, which is
  disabled in the released version of the code.

## 1.0.3

* Mistakes were made. Yanked and replaced by 1.0.4 above.

## 1.0.2

* Updates the library to use the renamed functions in Merlin 1.1.
* Adds additional validation checks to prevent identity points being used as
  part of a proof.  This does not appear to have security content, but is
  intended as a defense-in-depth mechanism.
  See [this comment][identity_comment] for more motivation.
* Documentation tweaks.

## 1.0.1

* Tweaks to crate metadata.
* Minor documentation changes.
* Adds a regression test for deserialize-and-verify for proofs created using
  v1.0.0, to ensure they continue to verify in future versions.

## 1.0.0

* Minor tweaks to the prerelease version.
* Preliminary support for R1CS proofs, but this feature is hard-disabled in the
  published crate.

## 1.0.0-pre.0

Initial prerelease version, supporting single and aggregated range proofs, and
multiparty proof aggregation.

[identity_comment]: https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r251916724

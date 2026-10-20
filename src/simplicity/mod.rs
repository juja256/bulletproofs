//! Simplicity verifiers for R1CS proofs (experimental, feature `simplicity`): a circuit on the
//! BP++ backend over secp256k1 with the SHA-256 transcript compiles into a Simplicity program
//! that verifies its proofs, bound to the spending transaction (docs/simplicity-verifier.md).

mod ir;
mod run;

pub use self::run::{dummy_env, dummy_env_with_output, sighash_of, Env, ExecError, Report};

/// The transcript label of the spending transaction's hash: the prover appends
/// `sighash_of(env)` under it, and the program replaces the message with `jet_sig_all_hash`.
pub const SIGHASH_LABEL: &[u8] = b"sighash";

//! Testing only (feature `cheats`): a prover that skips its own checks, so that downstream
//! soundness tests can check that the verifier rejects what it produces. Without the feature
//! only the crate-internal query exists and always answers "checked".

#[cfg(feature = "cheats")]
mod flag {
    use core::cell::Cell;

    thread_local! {
        static UNCHECKED: Cell<bool> = Cell::new(false);
    }

    /// While on (in this thread), the prover counts multiplicities only for lookups that equal
    /// a row (instead of refusing the others) and the BP++ prover proves unsatisfied circuits
    /// (instead of refusing them). The BP prover already proves violated constraints. The
    /// verifier is unaffected: such proofs must not verify.
    pub fn set_unchecked_prover(on: bool) {
        UNCHECKED.with(|u| u.set(on));
    }

    /// Run `f` with [`set_unchecked_prover`] on, and turn it off afterwards, also if `f` panics.
    pub fn with_unchecked_prover<R>(f: impl FnOnce() -> R) -> R {
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                set_unchecked_prover(false);
            }
        }
        set_unchecked_prover(true);
        let _reset = Reset;
        f()
    }

    pub(crate) fn unchecked() -> bool {
        UNCHECKED.with(|u| u.get())
    }
}

#[cfg(feature = "cheats")]
pub use self::flag::{set_unchecked_prover, with_unchecked_prover};
#[cfg(feature = "cheats")]
pub(crate) use self::flag::unchecked;

#[cfg(not(feature = "cheats"))]
pub(crate) fn unchecked() -> bool {
    false
}

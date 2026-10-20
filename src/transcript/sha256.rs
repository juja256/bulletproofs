//! The SHA-256 transcript (docs/sha256-transcript.md): a streaming SHA-256, cheap to recompute
//! where SHA-256 is the only hash, as with Simplicity's `sha_256_ctx_8_*` jets.

use core::convert::TryFrom;

use sha2::{Digest, Sha256};

use super::{TranscriptBackend, TranscriptRef};

const TAG: &[u8] = b"bulletproofs/transcript/sha256/v1";
const APPEND: u8 = 0x41;
const CHALLENGE: u8 = 0x43;
const RNG: u8 = 0x52;
/// At most 64 output blocks, so that the counter's first byte (< 64) never equals a record's
/// first byte (`APPEND`, `CHALLENGE`, `RNG`).
const MAX_CHALLENGE_BYTES: usize = 2048;

/// A Fiat–Shamir transcript built on SHA-256 alone, for verifiers that have no Keccak (and so
/// no Merlin), such as Simplicity on Liquid. Pass it wherever the crate takes a transcript.
///
/// The state is one running SHA-256: [`new`](Self::new) absorbs a tagged block and the
/// label, every message is absorbed as a length-prefixed record, and a challenge is the
/// finalization of a copy of the state with a block counter. The byte format is in
/// `docs/sha256-transcript.md`.
#[derive(Clone, Debug)]
pub struct Sha256Transcript {
    ctx: Sha256,
}

/// The length prefix of a record.
fn le32(n: usize) -> [u8; 4] {
    u32::try_from(n).expect("transcript item longer than 2^32 - 1 bytes").to_le_bytes()
}

impl Sha256Transcript {
    /// A transcript for the application `label`, as `merlin::Transcript::new`.
    pub fn new(label: &'static [u8]) -> Self {
        let t = Sha256::digest(TAG);
        let mut ctx = Sha256::new();
        ctx.update(t);
        ctx.update(t);
        let mut s = Sha256Transcript { ctx };
        s.append_message(b"dom-sep", label);
        s
    }

    fn record(&mut self, kind: u8, label: &[u8]) {
        self.ctx.update([kind]);
        self.ctx.update(le32(label.len()));
        self.ctx.update(label);
    }
}

impl TranscriptBackend for Sha256Transcript {
    fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        self.record(APPEND, label);
        self.ctx.update(le32(message.len()));
        self.ctx.update(message);
    }

    fn append_u64(&mut self, label: &'static [u8], x: u64) {
        self.append_message(label, &x.to_le_bytes());
    }

    fn challenge_bytes(&mut self, label: &'static [u8], dest: &mut [u8]) {
        assert!(
            (1..=MAX_CHALLENGE_BYTES).contains(&dest.len()),
            "a challenge has 1 to 2048 bytes"
        );
        self.record(CHALLENGE, label);
        self.ctx.update(le32(dest.len()));
        for (i, chunk) in dest.chunks_mut(32).enumerate() {
            let mut c = self.ctx.clone();
            c.update((i as u64).to_le_bytes());
            chunk.copy_from_slice(&c.finalize()[..chunk.len()]);
        }
    }

    fn build_rng(&self) -> merlin::TranscriptRngBuilder {
        let mut c = self.ctx.clone();
        c.update([RNG]);
        let mut t = merlin::Transcript::new(b"sha256-transcript-rng");
        t.append_message(b"state", &c.finalize());
        t.build_rng()
    }
}

impl TranscriptRef for Sha256Transcript {
    type Backend = Self;
    fn backend(&mut self) -> &mut Self {
        self
    }
    fn backend_ref(&self) -> &Self {
        self
    }
}

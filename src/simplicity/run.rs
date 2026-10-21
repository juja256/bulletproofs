//! Running programs as a node would, and the test environment.
//!
//! Adapted from simple-groth16's harness (`tools/harness/src/{env.rs, witness.rs, bin/hand.rs}`,
//! <https://github.com/BlockstreamResearch/simple-groth16>, MIT): the dummy transaction, word
//! values, and execution with the round trip through the consensus encoding.

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use ::simplicity::elements::taproot::ControlBlock;
use ::simplicity::elements::{self, confidential, AssetIssuance, BlockHash};
#[cfg(test)]
use ::simplicity::human_encoding::Forest;
use ::simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use ::simplicity::jet::Elements;
use ::simplicity::{types, BitIter, BitMachine, Cmr, RedeemNode, Value};

/// The Bit Machine's cell limit of consensus.
pub const MAX_CELLS: usize = 5_242_880;

/// A transaction environment programs run in.
pub type Env = ElementsEnv<Arc<elements::Transaction>>;

/// What running a program as a node would measured.
#[derive(Clone, Debug)]
pub struct Report {
    /// The static cost bound of the decoded (pruned) program, in milliweight units.
    pub cost_mwu: u64,
    /// The budget the input's witness stack pays for: 1000 · (stack bytes + 50), the stack
    /// being the witness data, the program, the CMR and the control block (one leaf).
    pub budget_mwu: u64,
    /// The pruned program's consensus encoding.
    pub program_bytes: usize,
    /// The witness data's encoding.
    pub witness_bytes: usize,
    /// Bit Machine memory bounds (consensus allows at most 5 242 880 cells).
    pub cells: usize,
    /// Bit Machine frame bound.
    pub frames: usize,
    /// The program's commitment Merkle root.
    pub cmr: Cmr,
}

/// Why a program did not run to completion.
#[derive(Clone, Debug)]
pub enum ExecError {
    /// The text is not a program.
    Parse(String),
    /// Types, witness or pruning failed (a failing assertion can show here).
    Finalize(String),
    /// The Bit Machine refused the program (resource bounds).
    Machine(String),
    /// The program failed when run (a failing assertion).
    Exec(String),
    /// The encoding did not round-trip.
    Decode(String),
    /// The Bit Machine needs more cells than consensus allows (5 242 880).
    Cells(usize),
    /// The cost exceeds what the witness pays for.
    Budget {
        /// The cost bound.
        cost_mwu: u64,
        /// 1000 · (stack bytes + 50).
        budget_mwu: u64,
    },
}

/// A transaction with one input and one output (simple-groth16's `env::dummy`).
pub fn dummy_env() -> Env {
    env_with(confidential::Value::default())
}

/// [`dummy_env`] with an explicit output value: another transaction, another `sig_all_hash`.
pub fn dummy_env_with_output(value: u64) -> Env {
    env_with(confidential::Value::Explicit(value))
}

fn env_with(value: confidential::Value) -> Env {
    let tx = elements::Transaction {
        version: 2,
        lock_time: elements::LockTime::ZERO,
        input: vec![elements::TxIn {
            previous_output: elements::OutPoint::default(),
            is_pegin: false,
            script_sig: elements::Script::new(),
            sequence: elements::Sequence::MAX,
            asset_issuance: AssetIssuance::default(),
            witness: elements::TxInWitness::default(),
        }],
        output: vec![elements::TxOut {
            asset: confidential::Asset::default(),
            value,
            nonce: confidential::Nonce::default(),
            script_pubkey: elements::Script::default(),
            witness: elements::TxOutWitness::default(),
        }],
    };
    let ctrl_blk: [u8; 33] = [
        0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff, 0x47, 0x33, 0x2f, 0xb7,
        0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52, 0x26, 0xd3, 0xbc, 0x09, 0xfc,
    ];
    let utxo = ElementsUtxo {
        script_pubkey: elements::Script::default(),
        asset: confidential::Asset::default(),
        value: confidential::Value::default(),
    };
    ElementsEnv::new(
        Arc::new(tx),
        vec![utxo],
        0,
        Cmr::from_byte_array([0; 32]),
        ControlBlock::from_slice(&ctrl_blk).expect("control block"),
        None,
        BlockHash::from_byte_array([0; 32]),
    )
}

/// The transaction hash `jet_sig_all_hash` gives in `env`: the bytes the prover appends to its
/// transcript under [`SIGHASH_LABEL`](crate::simplicity::SIGHASH_LABEL).
pub fn sighash_of(env: &Env) -> [u8; 32] {
    let h = env.c_tx_env().sighash_all();
    let mut out = [0u8; 32];
    out.copy_from_slice(h.as_ref());
    out
}

/// A word of `8 · bytes.len()` bits (a power of two), big-endian: bytes paired into a balanced tree.
pub(crate) fn word_value(bytes: &[u8]) -> Value {
    assert!(bytes.len().is_power_of_two(), "a word has 2^k bytes");
    let mut vals: VecDeque<Value> = bytes.iter().map(|b| Value::u8(*b)).collect();
    while vals.len() > 1 {
        let mut next = VecDeque::new();
        while let (Some(a), Some(b)) = (vals.pop_front(), vals.pop_front()) {
            next.push_back(Value::product(a, b));
        }
        vals = next;
    }
    vals.pop_front().expect("one value")
}

/// A bit.
#[allow(dead_code)] // used by the witness of a proof (points)
pub(crate) fn bit_value(b: bool) -> Value {
    Value::u1(b as u8)
}

/// The budget of a spend whose witness stack is (witness, program, CMR, control block of one
/// leaf), each with its one-byte length prefix (simple-groth16's `deploy spend`):
/// 1000 · (stack bytes + 50) mWU.
pub(crate) fn budget(program_bytes: usize, witness_bytes: usize) -> u64 {
    let stack = program_bytes + witness_bytes + 32 + 33 + 4 + 1;
    1000 * (stack as u64 + 50)
}

fn cost_of(n: &RedeemNode) -> u64 {
    n.bounds().cost.to_string().parse().expect("cost as an integer")
}

/// Parse `program` (human-readable encoding), prune it against `env` with `witness`, run it,
/// encode and decode it, check the CMR, run it again, and check its cost against the budget.
#[cfg(test)]
pub(crate) fn execute_text(program: &str, witness: &HashMap<Arc<str>, Value>, env: &Env) -> Result<Report, ExecError> {
    let forest = Forest::parse::<Elements>(program).map_err(|e| ExecError::Parse(e.to_string()))?;
    execute_forest(&forest, witness, env, true)
}

/// Run a program given as a combinator DAG, as a node would ([`execute_text`]'s checks).
pub(crate) fn execute_term(t: &crate::simplicity::term::Term, witness: &HashMap<Arc<str>, Value>, env: &Env, budgeted: bool) -> Result<Report, ExecError> {
    types::Context::with_context(|ctx| {
        let node = t.to_node(&ctx, Some(witness)).map_err(|e| ExecError::Finalize(e.to_string()))?;
        run_node(node, env, budgeted)
    })
}

#[cfg(test)]
pub(crate) fn execute_forest(forest: &Forest, witness: &HashMap<Arc<str>, Value>, env: &Env, budgeted: bool) -> Result<Report, ExecError> {
    types::Context::with_context(|ctx| {
        let node = forest.to_witness_node(&ctx, witness).ok_or_else(|| ExecError::Parse("no main".into()))?;
        run_node(node, env, budgeted)
    })
}

fn run_node(node: Arc<::simplicity::ConstructNode<'_>>, env: &Env, budgeted: bool) -> Result<Report, ExecError> {
    {
        let program = node.finalize_pruned(env).map_err(|e| ExecError::Finalize(e.to_string()))?;
        let mut mac = BitMachine::for_program(&program).map_err(|e| ExecError::Machine(e.to_string()))?;
        mac.exec(&program, env).map_err(|e| ExecError::Exec(e.to_string()))?;
        let (p, w) = program.to_vec_with_witness();
        let decoded = RedeemNode::decode::<_, _, Elements>(BitIter::from(p.iter().cloned()), BitIter::from(w.iter().cloned()))
            .map_err(|e| ExecError::Decode(e.to_string()))?;
        if decoded.cmr() != program.cmr() {
            return Err(ExecError::Decode("the CMR changed in the round trip".into()));
        }
        let mut mac = BitMachine::for_program(&decoded).map_err(|e| ExecError::Machine(e.to_string()))?;
        mac.exec(&decoded, env).map_err(|e| ExecError::Exec(e.to_string()))?;
        let bounds = decoded.bounds();
        let cost_mwu = cost_of(&decoded);
        let budget_mwu = budget(p.len(), w.len());
        if bounds.extra_cells > MAX_CELLS {
            return Err(ExecError::Cells(bounds.extra_cells));
        }
        if budgeted && cost_mwu > budget_mwu {
            return Err(ExecError::Budget { cost_mwu, budget_mwu });
        }
        Ok(Report {
            cost_mwu,
            budget_mwu,
            program_bytes: p.len(),
            witness_bytes: w.len(),
            cells: bounds.extra_cells,
            frames: bounds.extra_frames,
            cmr: program.cmr(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn wit(name: &str, v: ::simplicity::Value) -> HashMap<Arc<str>, ::simplicity::Value> {
        let mut m = HashMap::new();
        m.insert(Arc::from(name), v);
        m
    }

    const SIGHASH_PROGRAM: &str = "
w := witness : 1 -> 2^256
h := comp unit jet_sig_all_hash
main := comp (comp (pair h w) jet_eq_256) jet_verify
";

    #[test]
    fn sig_all_hash_matches_the_prover_bytes() {
        let env = dummy_env();
        let r = execute_text(SIGHASH_PROGRAM, &wit("w", word_value(&sighash_of(&env))), &env).unwrap();
        assert!(r.cost_mwu > 0);
        assert!(execute_text(SIGHASH_PROGRAM, &wit("w", word_value(&[0u8; 32])), &env).is_err());
    }

    #[test]
    fn another_output_changes_sig_all_hash() {
        let (a, b) = (dummy_env(), dummy_env_with_output(7));
        assert_ne!(sighash_of(&a), sighash_of(&b));
        assert!(execute_text(SIGHASH_PROGRAM, &wit("w", word_value(&sighash_of(&a))), &b).is_err());
    }

    /// Ten scalar multiplications (727k mWU) against a 32-byte witness (82k mWU of budget).
    #[test]
    fn budget_is_enforced() {
        let mut text = String::from("w := witness : 1 -> 2^256\nk := comp unit (const 0x0000000000000000000000000000000000000000000000000000000000000001)\n");
        // gej of the generator: ((x, y), 1)
        text.push_str("g := comp unit (pair (pair (const 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798) (const 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)) (const 0x0000000000000000000000000000000000000000000000000000000000000001))\n");
        // a witness node has one path from the root: the scalar is a constant, the witness only
        // pays for the budget
        text.push_str("s0 := comp (pair k g) jet_scale\n");
        for i in 1..10 {
            text.push_str(&format!("s{} := comp (pair k s{}) jet_scale\n", i, i - 1));
        }
        text.push_str("main := comp (pair (comp s9 jet_gej_is_infinity) (comp w jet_scalar_is_zero)) (case unit unit)\n");
        match execute_text(&text, &wit("w", word_value(&[1u8; 32])), &dummy_env()) {
            Err(ExecError::Budget { cost_mwu, budget_mwu }) => assert!(cost_mwu > budget_mwu),
            other => panic!("expected a budget error, got {:?}", other.map(|r| r.cost_mwu)),
        }
    }
}

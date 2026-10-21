//! Simplicity expressions as a DAG of combinators, built into rust-simplicity nodes directly
//! (no text to parse). `Arc` sharing is DAG sharing: a shared term is one node with one type, so
//! only terms of a fixed type are shared (constants `1 -> T`, functions).

use core::convert::TryInto;
use std::collections::HashMap;
use std::sync::Arc;

use ::simplicity::jet::Elements;
use ::simplicity::node::{CoreConstructible, WitnessConstructible};
use ::simplicity::{types, Cmr, CommitNode, ConstructNode, Value, Word};

/// A Simplicity expression: a node of a DAG of combinators.
#[derive(Clone)]
pub(crate) struct Term(Arc<Inner>);

enum Inner {
    Iden,
    Unit,
    Take(Term),
    Drop(Term),
    Comp(Term, Term),
    Pair(Term, Term),
    Case(Term, Term),
    /// `assertr #{unit} t`: fails on the left branch.
    AssertR(Term),
    Jet(Elements),
    Const(Word),
    Witness(Arc<str>),
}

impl Term {
    fn new(i: Inner) -> Term {
        Term(Arc::new(i))
    }
    pub(crate) fn iden() -> Term {
        Term::new(Inner::Iden)
    }
    pub(crate) fn unit() -> Term {
        Term::new(Inner::Unit)
    }
    pub(crate) fn take(t: &Term) -> Term {
        Term::new(Inner::Take(t.clone()))
    }
    pub(crate) fn drop_(t: &Term) -> Term {
        Term::new(Inner::Drop(t.clone()))
    }
    pub(crate) fn comp(a: &Term, b: &Term) -> Term {
        Term::new(Inner::Comp(a.clone(), b.clone()))
    }
    pub(crate) fn pair(a: &Term, b: &Term) -> Term {
        Term::new(Inner::Pair(a.clone(), b.clone()))
    }
    pub(crate) fn case(a: &Term, b: &Term) -> Term {
        Term::new(Inner::Case(a.clone(), b.clone()))
    }
    pub(crate) fn assertr(t: &Term) -> Term {
        Term::new(Inner::AssertR(t.clone()))
    }
    /// A jet by name (without `jet_`).
    pub(crate) fn jet(name: &str) -> Term {
        let j: Elements = name.parse().unwrap_or_else(|_| panic!("unknown jet {}", name));
        Term::new(Inner::Jet(j))
    }
    /// A constant word (`1 -> 2^(8·len)`), big-endian bytes; one byte 0/1 with `bit`.
    pub(crate) fn word(bytes: &[u8]) -> Term {
        let w = match bytes.len() {
            1 => Word::u8(bytes[0]),
            2 => Word::u16(u16::from_be_bytes([bytes[0], bytes[1]])),
            4 => Word::u32(u32::from_be_bytes(bytes.try_into().unwrap())),
            8 => Word::u64(u64::from_be_bytes(bytes.try_into().unwrap())),
            16 => Word::u128(u128::from_be_bytes(bytes.try_into().unwrap())),
            32 => Word::u256(bytes.try_into().unwrap()),
            n => panic!("no word of {} bytes", n),
        };
        Term::new(Inner::Const(w))
    }
    /// A constant bit (`1 -> 2`).
    pub(crate) fn bit(b: bool) -> Term {
        Term::new(Inner::Const(Word::u1(b as u8)))
    }
    /// A named witness value.
    pub(crate) fn witness(name: &str) -> Term {
        Term::new(Inner::Witness(Arc::from(name)))
    }

    /// The node, witness values from `w` (none: a commitment-time program).
    pub(crate) fn to_node<'b>(&self, ctx: &types::Context<'b>, w: Option<&HashMap<Arc<str>, Value>>) -> Result<Arc<ConstructNode<'b>>, types::Error> {
        let mut memo: HashMap<*const Inner, Arc<ConstructNode<'b>>> = HashMap::new();
        self.build(ctx, w, &mut memo)
    }

    fn build<'b>(&self, ctx: &types::Context<'b>, w: Option<&HashMap<Arc<str>, Value>>, memo: &mut HashMap<*const Inner, Arc<ConstructNode<'b>>>) -> Result<Arc<ConstructNode<'b>>, types::Error> {
        let key = Arc::as_ptr(&self.0);
        if let Some(n) = memo.get(&key) {
            return Ok(n.clone());
        }
        type N<'b> = Arc<ConstructNode<'b>>;
        let n: N<'b> = match &*self.0 {
            Inner::Iden => N::iden(ctx),
            Inner::Unit => N::unit(ctx),
            Inner::Take(t) => N::take(&t.build(ctx, w, memo)?),
            Inner::Drop(t) => N::drop_(&t.build(ctx, w, memo)?),
            Inner::Comp(a, b) => {
                let (x, y) = (a.build(ctx, w, memo)?, b.build(ctx, w, memo)?);
                N::comp(&x, &y)?
            }
            Inner::Pair(a, b) => {
                let (x, y) = (a.build(ctx, w, memo)?, b.build(ctx, w, memo)?);
                N::pair(&x, &y)?
            }
            Inner::Case(a, b) => {
                let (x, y) = (a.build(ctx, w, memo)?, b.build(ctx, w, memo)?);
                N::case(&x, &y)?
            }
            Inner::AssertR(t) => N::assertr(Cmr::unit(), &t.build(ctx, w, memo)?)?,
            Inner::Jet(j) => N::jet(ctx, j),
            Inner::Const(word) => N::const_word(ctx, word.shallow_clone()),
            Inner::Witness(name) => N::witness(ctx, w.and_then(|m| m.get(name).cloned())),
        };
        memo.insert(key, n.clone());
        Ok(n)
    }

    /// The commitment-time program (types finalized, no witness).
    pub(crate) fn commit(&self) -> Result<Arc<CommitNode>, String> {
        types::Context::with_context(|ctx| {
            let n = self.to_node(&ctx, None).map_err(|e| e.to_string())?;
            n.finalize_types().map_err(|e| e.to_string())
        })
    }

    /// The program in the human-readable encoding (an artifact).
    pub(crate) fn text(&self) -> Result<String, String> {
        Ok(::simplicity::human_encoding::Forest::from_program(self.commit()?).string_serialize())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplicity::ir::tests_support::{arithmetic_prog, arithmetic_witness};
    use crate::simplicity::run::{dummy_env, execute_term};
    use std::collections::HashMap;

    #[test]
    fn term_executes_with_witness() {
        let p = arithmetic_prog();
        let t = p.to_term();
        assert!(execute_term(&t, &arithmetic_witness(0), &dummy_env(), false).is_ok());
        assert!(execute_term(&t, &arithmetic_witness(1), &dummy_env(), false).is_err());
    }

    /// A constant is `1 -> T`, read with `comp unit k` from environments of any type.
    #[test]
    fn shared_const_in_two_environments() {
        let k = Term::word(&[7u8; 32]);
        // environment 1: unit; environment 2: (word, unit)
        let read = |_: ()| Term::comp(&Term::unit(), &k);
        let eq = Term::comp(&Term::pair(&read(()), &read(())), &Term::jet("eq_256"));
        let step1 = Term::pair(&read(()), &Term::unit()); // 1 -> (word, 1)
        let check = Term::comp(&Term::comp(&Term::pair(&Term::take(&Term::iden()), &read(())), &Term::jet("eq_256")), &Term::jet("verify"));
        let main = Term::comp(&step1, &Term::comp(&Term::pair(&check, &Term::comp(&eq, &Term::jet("verify"))), &Term::unit()));
        assert!(execute_term(&main, &HashMap::new(), &dummy_env(), false).is_ok());
    }
}

//! Tests that need the crate-private randomized constraints: upstream dalek's gadgets (a
//! shuffle, a range proof with a reciprocal argument), the golden proofs of upstream and the
//! refusal of randomized constraints by BP++ and the Simplicity compiler.

#![allow(non_snake_case)]

mod golden;
mod randomized;
mod reciprocal;
mod upstream;

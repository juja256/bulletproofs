//! The circuit builder (spec §7): the same gadgets proven with both backends, pinned costs,
//! rejected witnesses and statements.

#![allow(non_snake_case)]

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

type Lc = LinearCombination;

fn backends() -> Vec<Backend> {
    #[allow(unused_mut)]
    let mut b = vec![Backend::Bp];
    #[cfg(feature = "bppp")]
    b.push(Backend::Bppp);
    b
}

/// The byte table and the nibble XOR table `(a, b, a ^ b)`.
struct Tables {
    byte: TableId,
    nib: TableId,
    xor: TableId,
}

fn tables<CS: CircuitBuilder>(cs: &mut CS) -> Result<Tables, R1CSError> {
    let byte = cs.table((0..256u64).map(|x| vec![x]).collect())?;
    let nib = cs.table((0..16u64).map(|x| vec![x]).collect())?;
    let xor = cs.table((0..256u64).map(|x| vec![x >> 4, x & 15, (x >> 4) ^ (x & 15)]).collect())?;
    Ok(Tables { byte, nib, xor })
}

/// `x < 2^32`: four bytes from the byte table, `x = sum 256^i b_i`.
fn range32<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, x: Lc, value: Option<u64>) -> Result<Vec<Variable>, R1CSError> {
    let mut sum = Lc::default();
    let mut bytes = Vec::new();
    for i in 0..4 {
        let b = cs.lookup_value(t.byte, value.map(|v| (v >> (8 * i)) & 255))?;
        sum = sum + b * Scalar::from(1u64 << (8 * i));
        bytes.push(b);
    }
    cs.constrain(x - sum);
    Ok(bytes)
}

/// Nibbles of a byte, from the nibble table.
fn nibbles<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, byte: Variable, value: Option<u64>) -> Result<(Variable, Variable), R1CSError> {
    let nib = t.nib;
    let hi = cs.lookup_value(nib, value.map(|v| v >> 4))?;
    let lo = cs.lookup_value(nib, value.map(|v| v & 15))?;
    cs.constrain(byte - hi * Scalar::from(16u64) - lo);
    Ok((hi, lo))
}

/// `z = x ^ y` for bytes, nibble by nibble through the XOR table; returns `z`.
fn xor8<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, x: Variable, y: Variable, v: Option<(u64, u64)>) -> Result<Variable, R1CSError> {
    let (xh, xl) = nibbles(cs, t, x, v.map(|v| v.0))?;
    let (yh, yl) = nibbles(cs, t, y, v.map(|v| v.1))?;
    let nib = t.nib;
    let zh = cs.lookup_value(nib, v.map(|v| (v.0 ^ v.1) >> 4))?;
    let zl = cs.lookup_value(nib, v.map(|v| (v.0 ^ v.1) & 15))?;
    cs.lookup(t.xor, &[xh.into(), yh.into(), zh.into()])?;
    cs.lookup(t.xor, &[xl.into(), yl.into(), zl.into()])?;
    let z = cs.witness(v.map(|v| Scalar::from(v.0 ^ v.1)))?;
    cs.constrain(z - zh * Scalar::from(16u64) - zl);
    Ok(z)
}

/// A memory permutation: the multiset of `(address, value)` writes equals that of the reads,
/// with addresses and values bytes.
fn memory<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, writes: &[(u64, u64)], reads: Option<&[(u64, u64)]>, n: usize) -> Result<(), R1CSError> {
    let mut arg = cs.reciprocal(2)?;
    for i in 0..n {
        let w = writes.get(i).copied();
        let a = cs.lookup_value(t.byte, w.map(|w| w.0))?;
        let v = cs.lookup_value(t.byte, w.map(|w| w.1))?;
        arg.add(vec![a.into(), v.into()]);
    }
    for i in 0..n {
        let r = reads.map(|r| r[i]);
        let a = cs.lookup_value(t.byte, r.map(|r| r.0))?;
        let v = cs.lookup_value(t.byte, r.map(|r| r.1))?;
        arg.sub(vec![a.into(), v.into()]);
    }
    cs.finish_reciprocal(arg)
}

/// A MACT-style balance: committed `(amount, asset type)` pairs, `sum_in a/(X + t) - sum_out
/// a/(X + t) = 0`, every output amount below `2^32` (`range32`).
fn balance<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, ins: &[(Variable, Variable)], outs: &[(Variable, Variable)], out_amounts: Option<&[u64]>) -> Result<(), R1CSError> {
    let mut arg = cs.reciprocal(1)?;
    for (a, ty) in ins {
        arg.add_weighted((*a).into(), vec![(*ty).into()]);
    }
    for (i, (a, ty)) in outs.iter().enumerate() {
        arg.add_weighted(-Lc::from(*a), vec![(*ty).into()]);
        range32(cs, t, (*a).into(), out_amounts.map(|o| o[i]))?;
    }
    cs.finish_reciprocal(arg)
}

/// The prover's private data; the committed inputs are `(x, a_in, t_in, a_out1, t_out1,
/// a_out2, t_out2)`.
struct Private {
    xy: (u64, u64),
    writes: Vec<(u64, u64)>,
    reads: Vec<(u64, u64)>,
    outs: Vec<u64>,
}

/// All four gadgets in one statement.
fn statement<CS: CircuitBuilder>(cs: &mut CS, V: &[Variable], p: Option<&Private>, x: Option<u64>) -> Result<(), R1CSError> {
    let t = tables(cs)?;
    // range32 of a committed value
    range32(cs, &t, V[0].into(), x)?;
    // XOR of two private bytes, result checked against a product
    let xv = cs.witness(p.map(|p| Scalar::from(p.xy.0)))?;
    let yv = cs.witness(p.map(|p| Scalar::from(p.xy.1)))?;
    let z = xor8(cs, &t, xv, yv, p.map(|p| p.xy))?;
    cs.product(z.into(), Scalar::ONE.into(), z + Scalar::ZERO)?;
    // memory permutation
    memory(cs, &t, &p.map(|p| p.writes.clone()).unwrap_or_default(), p.map(|p| &p.reads[..]), 3)?;
    // balance
    balance(cs, &t, &[(V[1], V[2])], &[(V[3], V[4]), (V[5], V[6])], p.map(|p| &p.outs[..]))?;
    Ok(())
}

fn values() -> (Vec<u64>, Private) {
    let vals = vec![0xdead_beef, 1000, 77, 400, 77, 600, 77];
    let p = Private { xy: (0x5a, 0xc3), writes: vec![(1, 10), (2, 20), (1, 30)], reads: vec![(1, 30), (1, 10), (2, 20)], outs: vec![400, 600] };
    (vals, p)
}

fn prove(backend: Backend, vals: &[u64], p: &Private, bp: &BulletproofGens) -> Result<(R1CSProof, Vec<CompressedRistretto>, Cost), R1CSError> {
    let pc = PedersenGens::default();
    let mut t = Transcript::new(b"builder");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(backend);
    let (V, vars): (Vec<_>, Vec<_>) = vals.iter().enumerate().map(|(i, v)| prover.commit(Scalar::from(*v), Scalar::from(i as u64 + 5))).unzip();
    statement(&mut prover, &vars, Some(p), Some(vals[0]))?;
    let cost = prover.cost();
    let proof = prover.prove_with_rng(bp, &mut ChaCha20Rng::seed_from_u64(1))?;
    Ok((proof, V, cost))
}

fn verify(backend: Backend, proof: &R1CSProof, V: &[CompressedRistretto], bp: &BulletproofGens) -> Result<Cost, R1CSError> {
    let pc = PedersenGens::default();
    let mut t = Transcript::new(b"builder");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(backend);
    let vars: Vec<Variable> = V.iter().map(|v| verifier.commit(*v)).collect();
    statement(&mut verifier, &vars, None, None)?;
    let cost = verifier.cost();
    verifier.verify(proof, &pc, bp)?;
    Ok(cost)
}

#[test]
fn gadgets_on_both_backends() {
    let bp = BulletproofGens::new(2048, 1);
    let (vals, p) = values();
    for backend in backends() {
        let (proof, V, cost) = prove(backend, &vals, &p, &bp).unwrap();
        let parsed = R1CSProof::from_bytes(&proof.to_bytes()).unwrap();
        assert_eq!(verify(backend, &parsed, &V, &bp).unwrap(), cost);
        // private terms: range32 4, xor8 8 (6 nibbles, 2 xor rows), memory 12 + 6, balance
        // 3 + 8 = 41; witnesses 33 + multiplicities 256 + 16 + 256 = 561, 281 pairs; 1 product
        // N_lin: 7 input copies + 561 witnesses - 42 norm slots
        assert_eq!(cost, Cost { bp_phase1: 282, bp_phase2: 41, bppp_gates: 42, bppp_lin: 526 }, "{:?}", backend);
        // exactly the capacity the cost asks for suffices, one less does not
        let need = cost.gens_capacity(backend);
        assert_eq!(need, if backend == Backend::Bp { 512 } else { 532 });
        assert!(prove(backend, &vals, &p, &BulletproofGens::new(need, 1)).is_ok());
        assert!(matches!(prove(backend, &vals, &p, &BulletproofGens::new(need - 1, 1)), Err(R1CSError::InvalidGeneratorsLength)));
    }
}

/// The prover refuses, or its proof does not verify.
fn rejected(backend: Backend, vals: &[u64], p: &Private, bp: &BulletproofGens) -> bool {
    match prove(backend, vals, p, bp) {
        Err(_) => true,
        Ok((proof, V, _)) => verify(backend, &proof, &V, bp).is_err(),
    }
}

#[test]
fn wrong_witnesses_are_refused() {
    let bp = BulletproofGens::new(2048, 1);
    let (vals, _) = values();
    for backend in backends() {
        // a value out of range: its bytes do not add up to it
        let mut v = vals.clone();
        v[0] = 1 << 32;
        assert!(rejected(backend, &v, &values().1, &bp), "{:?}", backend);
        // a nibble outside the table: the prover finds no row
        let mut q = values().1;
        q.xy = (0x5a, 0x1c3);
        assert!(matches!(prove(backend, &vals, &q, &bp), Err(R1CSError::GadgetError { .. })));
        // reads that are not a permutation of the writes
        let mut q = values().1;
        q.reads[0] = (1, 31);
        assert!(rejected(backend, &vals, &q, &bp), "{:?}", backend);
        // unbalanced amounts
        let mut v = vals.clone();
        v[5] = 601;
        let mut q = values().1;
        q.outs[1] = 601;
        assert!(rejected(backend, &v, &q, &bp), "{:?}", backend);
        // another asset type for one output
        let mut v = vals.clone();
        v[6] = 78;
        assert!(rejected(backend, &v, &values().1, &bp), "{:?}", backend);
    }
}

#[test]
fn proofs_of_one_backend_do_not_verify_with_the_other() {
    let bp = BulletproofGens::new(2048, 1);
    let (vals, p) = values();
    let bs = backends();
    for (i, a) in bs.iter().enumerate() {
        let (proof, V, _) = prove(*a, &vals, &p, &bp).unwrap();
        for (j, b) in bs.iter().enumerate() {
            if i != j {
                assert!(verify(*b, &proof, &V, &bp).is_err());
            }
        }
    }
}

/// A small statement exercising the copies of §7.6: numerators and public coefficients that
/// read `MultiplierRight` (the right wire of `allocate`), tuple components on `w_L` and `w_R`,
/// constants in coefficients, a product with constants.
fn copies<CS: CircuitBuilder>(cs: &mut CS, V: &[Variable], p: Option<[u64; 3]>) -> Result<(), R1CSError> {
    let s = |x: u64| Scalar::from(x);
    let a = cs.allocate(p.map(|p| s(p[0])))?; // MultiplierLeft(0)
    let b = cs.allocate(p.map(|p| s(p[1])))?; // MultiplierRight(0)
    let t = cs.table((0..8u64).map(|x| vec![x]).collect())?;
    cs.lookup(t, &[b.into()])?; // b < 8
    cs.lookup(t, &[a.into()])?;
    let w = cs.witness(p.map(|p| s(p[2])))?;
    cs.product(a + 1u64, b.into(), w - V[0] + Scalar::ONE)?; // (a + 1) b = w - v + 1
    // b / (X + (a, b)) - b / (X + (a, b)) + (2b - 10) / (X + (1, 2))
    let mut r = cs.reciprocal(2)?;
    r.add_weighted(b + 0u64, vec![a.into(), b.into()]);
    r.add_weighted(-Lc::from(b), vec![a.into(), b.into()]);
    r.add_public(b * Scalar::from(2u64) - Scalar::from(10u64), vec![1, 2]); // 0 for b = 5
    cs.finish_reciprocal(r)
}

fn prove_small<F>(backend: Backend, v: u64, gadget: F) -> Result<(R1CSProof, CompressedRistretto, Cost), R1CSError>
where
    F: Fn(&mut Prover<&mut Transcript>, Variable) -> Result<(), R1CSError>,
{
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    let mut t = Transcript::new(b"small");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(backend);
    let (V, x) = prover.commit(Scalar::from(v), Scalar::from(3u64));
    gadget(&mut prover, x)?;
    let cost = prover.cost();
    Ok((prover.prove_with_rng(&bp, &mut ChaCha20Rng::seed_from_u64(2))?, V, cost))
}

fn verify_small<F>(backend: Backend, proof: &R1CSProof, V: CompressedRistretto, gadget: F) -> Result<(), R1CSError>
where
    F: Fn(&mut Verifier<&mut Transcript>, Variable) -> Result<(), R1CSError>,
{
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(64, 1);
    let mut t = Transcript::new(b"small");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(backend);
    let x = verifier.commit(V);
    gadget(&mut verifier, x)?;
    verifier.verify(proof, &pc, &bp)
}

#[test]
fn copies_of_right_wires() {
    // a = 2, b = 5, w = (a + 1) b + v - 1 with v = 4: 18; the public coefficient 2b - 10 = 0
    for backend in backends() {
        let (proof, V, cost) = prove_small(backend, 4, |cs, x| copies(cs, &[x], Some([2, 5, 18]))).unwrap();
        // BP++: w_O = 1 output + 1 input copy + 9 witnesses + 3 copies of right wires (two
        // numerators, one coefficient) + 4 copies of tuple components (a, b twice: w_L, w_R are
        // committed after eta), 6 in n_O
        assert_eq!(cost, Cost { bp_phase1: 1 + 5 + 1, bp_phase2: 4, bppp_gates: 4 + 1 + 1, bppp_lin: 12 });
        verify_small(backend, &proof, V, |cs, x| copies(cs, &[x], None)).unwrap();
        // a wrong w: refused or rejected
        let bad = prove_small(backend, 4, |cs, x| copies(cs, &[x], Some([2, 5, 19])));
        assert!(bad.map(|(p, V, _)| verify_small(backend, &p, V, |cs, x| copies(cs, &[x], None)).is_err()).unwrap_or(true));
    }
}

/// Builder mode without gates: one padding multiplier (§7.6); witnesses and constraints only.
#[test]
fn no_gates() {
    for backend in backends() {
        let g = |cs: &mut Prover<&mut Transcript>, x: Variable| {
            let w = cs.witness(Some(Scalar::from(4u64)))?;
            cs.constrain(w - x);
            Ok(())
        };
        let gv = |cs: &mut Verifier<&mut Transcript>, x: Variable| {
            let w = cs.witness(None)?;
            cs.constrain(w - x);
            Ok(())
        };
        let (proof, V, cost) = prove_small(backend, 4, g).unwrap();
        // w_O = the padding output, the input copy, the witness; one norm slot
        assert_eq!(cost, Cost { bp_phase1: 1, bp_phase2: 0, bppp_gates: 1, bppp_lin: 2 });
        verify_small(backend, &proof, V, gv).unwrap();
        // a wrong value: rejected
        if let Ok((proof, V, _)) = prove_small(backend, 5, g) {
            assert!(verify_small(backend, &proof, V, gv).is_err());
        }
    }
}

#[cfg(feature = "bppp")]
#[test]
fn bppp_builder_rules() {
    let b = Backend::Bppp;
    let g = |cs: &mut Prover<&mut Transcript>, x: Variable| copies(cs, &[x], Some([2, 5, 18]));
    let gv = |cs: &mut Verifier<&mut Transcript>, x: Variable| copies(cs, &[x], None);
    let (proof, V, _) = prove_small(b, 4, g).unwrap();
    // randomized constraints are refused on both sides
    let rand_p = |cs: &mut Prover<&mut Transcript>, x: Variable| {
        g(cs, x)?;
        cs.specify_randomized_constraints(|_| Ok(()))
    };
    let rand_v = |cs: &mut Verifier<&mut Transcript>, x: Variable| {
        gv(cs, x)?;
        cs.specify_randomized_constraints(|_| Ok(()))
    };
    assert!(matches!(prove_small(b, 4, rand_p), Err(R1CSError::GadgetError { .. })));
    assert!(matches!(verify_small(b, &proof, V, rand_v), Err(R1CSError::GadgetError { .. })));
    // a verifier without builder operations (spec §6) rejects a builder proof, and conversely
    let plain_p = |cs: &mut Prover<&mut Transcript>, x: Variable| {
        cs.constrain(x - 4u64);
        Ok(())
    };
    let plain_v = |cs: &mut Verifier<&mut Transcript>, x: Variable| {
        cs.constrain(x - 4u64);
        Ok(())
    };
    assert!(verify_small(b, &proof, V, plain_v).is_err());
    let (plain, V2, _) = prove_small(b, 4, plain_p).unwrap();
    verify_small(b, &plain, V2, plain_v).unwrap();
    assert!(verify_small(b, &plain, V2, gv).is_err());
    // malformed encodings
    let bytes = proof.to_bytes();
    assert_eq!(bytes[0], 3);
    assert!(R1CSProof::from_bytes(&bytes[..bytes.len() - 1]).is_err());
    assert!(R1CSProof::from_bytes(&bytes[..10]).is_err());
    for (at, delta) in [(1usize, 1u8), (9, 1)] {
        let mut x = bytes.clone();
        x[at] = x[at].wrapping_add(delta);
        match R1CSProof::from_bytes(&x) {
            Ok(p) => assert!(verify_small(b, &p, V, gv).is_err()),
            Err(_) => {}
        }
    }
    let mut x = bytes.clone();
    x[17] ^= 1;
    if let Ok(p) = R1CSProof::from_bytes(&x) {
        assert!(verify_small(b, &p, V, gv).is_err());
    }
}

#[cfg(feature = "bppp")]
#[test]
fn proof_sizes() {
    let bp = BulletproofGens::new(2048, 1);
    let (vals, p) = values();
    let size = |b| prove(b, &vals, &p, &bp).unwrap().0.to_bytes().len();
    // BP: 282 + 41 = 323 multipliers, padded to 2^9: 11 points, 3 scalars, 9 rounds, 2 scalars.
    // BP++: 42 gates; w_O = 7 input copies + 561 witnesses, 42 in n_O, N_lin = 526.
    assert_eq!(size(Backend::Bp), 1 + 32 * (11 + 3 + 2 * 9 + 2));
    assert_eq!(size(Backend::Bppp), 17 + 32 * 4 + bppp_wnla(7 + 526, 42));
}

/// Size of the norm argument (spec §2.2, §2.5) for lengths `a`, `b`.
#[cfg(feature = "bppp")]
fn bppp_wnla(mut a: usize, mut b: usize) -> usize {
    let mut rounds = 0;
    while a / 2 + b / 2 >= 3 {
        a = (a + 1) / 2;
        b = (b + 1) / 2;
        rounds += 1;
    }
    32 * (2 * rounds + a + b)
}

/// A failed operation records nothing (spec §7.2): `lookup_value` on a two-column table does
/// not leave a witness behind, on the prover or the verifier.
#[test]
fn failed_operations_record_nothing() {
    let pc = PedersenGens::default();
    let mut t = Transcript::new(b"x");
    let mut p = Prover::new(&pc, &mut t);
    let mut t2 = Transcript::new(b"x");
    let mut v = Verifier::new(&mut t2);
    fn go<CS: CircuitBuilder>(cs: &mut CS, val: Option<u64>) {
        let two = cs.table(vec![vec![0, 0]]).unwrap();
        let one = cs.table(vec![vec![0]]).unwrap();
        let before = cs.cost();
        assert!(cs.lookup_value(two, val).is_err());
        assert!(cs.lookup(one, &[Variable::Witness(0).into()]).is_err(), "no witness 0");
        assert_eq!(cs.cost(), before);
        assert_eq!(cs.witness(val.map(Scalar::from)).unwrap(), Variable::Witness(0));
    }
    go(&mut p, Some(0));
    go(&mut v, None);
}

/// Constraints on variables that do not exist are a `GadgetError` on both backends, with or
/// without `parallel` (found in review: BP panicked serially and dropped the term in parallel;
/// a `Witness` one past the last aliased the zero half of the last witness pair).
#[test]
fn constraints_on_missing_variables_are_errors() {
    let bad = [Variable::Witness(1), Variable::Witness(1000), Variable::MultiplierLeft(7), Variable::Committed(1)];
    for backend in backends() {
        for &y in &bad {
            let gp = move |cs: &mut Prover<&mut Transcript>, x: Variable| {
                cs.witness(Some(Scalar::from(4u64)))?;
                cs.constrain(y - x);
                Ok(())
            };
            let gv = move |cs: &mut Verifier<&mut Transcript>, x: Variable| {
                cs.witness(None)?;
                cs.constrain(y - x);
                Ok(())
            };
            assert!(matches!(prove_small(backend, 0, gp), Err(R1CSError::GadgetError { .. })), "{:?} {:?}", backend, y);
            // a proof of the honest statement, presented to a verifier with the bad constraint
            let ok = |cs: &mut Prover<&mut Transcript>, x: Variable| {
                cs.witness(Some(Scalar::from(4u64)))?;
                cs.constrain(x - 0u64);
                Ok(())
            };
            let (proof, V, _) = prove_small(backend, 0, ok).unwrap();
            assert!(matches!(verify_small(backend, &proof, V, gv), Err(R1CSError::GadgetError { .. })), "{:?} {:?}", backend, y);
        }
    }
    // also without builder operations (BP; BP++ §6 already checked)
    let gp = |cs: &mut Prover<&mut Transcript>, x: Variable| {
        cs.constrain(Variable::MultiplierOutput(3) - x);
        Ok(())
    };
    assert!(matches!(prove_small(Backend::Bp, 0, gp), Err(R1CSError::GadgetError { .. })));
}

/// Builder mode starts with the first successful builder operation (review): a statement whose
/// only builder operations failed is proven as in spec §6 (proof tag 2).
#[cfg(feature = "bppp")]
#[test]
fn failed_operations_do_not_enter_builder_mode() {
    let g = |cs: &mut Prover<&mut Transcript>, x: Variable| {
        assert!(cs.table(vec![vec![]]).is_err());
        assert!(cs.product(Variable::Witness(3).into(), x.into(), x.into()).is_err());
        let r = cs.reciprocal(1)?;
        let mut r2 = r.clone();
        r2.add(vec![Variable::Witness(9).into()]);
        assert!(cs.finish_reciprocal(r2).is_err());
        cs.constrain(x - 0u64);
        Ok(())
    };
    let gv = |cs: &mut Verifier<&mut Transcript>, x: Variable| {
        assert!(cs.table(vec![vec![]]).is_err());
        assert!(cs.product(Variable::Witness(3).into(), x.into(), x.into()).is_err());
        let r = cs.reciprocal(1)?;
        let mut r2 = r.clone();
        r2.add(vec![Variable::Witness(9).into()]);
        assert!(cs.finish_reciprocal(r2).is_err());
        cs.constrain(x - 0u64);
        Ok(())
    };
    let (proof, V, _) = prove_small(Backend::Bppp, 0, g).unwrap();
    assert_eq!(proof.to_bytes()[0], 2);
    verify_small(Backend::Bppp, &proof, V, gv).unwrap();
}

/// `CircuitBuilder` is object safe: gadgets can take `&mut dyn CircuitBuilder`.
#[test]
fn object_safe() {
    fn gadget(cs: &mut dyn CircuitBuilder, v: Option<u64>) -> Result<Variable, R1CSError> {
        let t = cs.table((0..4u64).map(|x| vec![x]).collect())?;
        cs.lookup_value(t, v)
    }
    for backend in backends() {
        let p = |cs: &mut Prover<&mut Transcript>, x: Variable| {
            let y = gadget(cs, Some(3))?;
            cs.constrain(y - x);
            Ok(())
        };
        let v = |cs: &mut Verifier<&mut Transcript>, x: Variable| {
            let y = gadget(cs, None)?;
            cs.constrain(y - x);
            Ok(())
        };
        let (proof, V, _) = prove_small(backend, 3, p).unwrap();
        verify_small(backend, &proof, V, v).unwrap();
    }
}

/// bpvm's `bitop` pattern (spec §7.3): a 32-bit XOR as 8 lookups of fresh nibbles
/// `(a_i, b_i, a_i ^ b_i)` into one table, with no range checks on the nibbles — the lookup
/// bounds them. Costs 8 BP++ gates. A decomposition that only packs right (a nibble of 16 and
/// a borrow from the next one) is not a row: the prover refuses.
#[test]
fn xor32_with_unbounded_nibbles() {
    fn xor32<CS: CircuitBuilder>(cs: &mut CS, x: Variable, y: Variable, nibbles: Option<[(u64, u64); 8]>) -> Result<Variable, R1CSError> {
        let t = cs.table((0..256u64).map(|v| vec![v >> 4, v & 15, (v >> 4) ^ (v & 15)]).collect())?;
        let (mut sx, mut sy, mut sz) = (Lc::default(), Lc::default(), Lc::default());
        for i in 0..8 {
            let n = nibbles.map(|n| n[i]);
            let a = cs.witness(n.map(|n| Scalar::from(n.0)))?;
            let b = cs.witness(n.map(|n| Scalar::from(n.1)))?;
            // the honest output nibble; with a cheating decomposition no row matches anyway
            let r = cs.witness(n.map(|n| Scalar::from((n.0 ^ n.1) & 15)))?;
            cs.lookup(t, &[a.into(), b.into(), r.into()])?;
            let w = Scalar::from(1u64 << (4 * i));
            sx = sx + a * w;
            sy = sy + b * w;
            sz = sz + r * w;
        }
        cs.constrain(sx - x);
        cs.constrain(sy - y);
        let z = cs.witness(nibbles.map(|n| Scalar::from((0..8).map(|i| ((n[i].0 ^ n[i].1) & 15) << (4 * i)).sum::<u64>())))?;
        cs.constrain(sz - z);
        Ok(z)
    }
    let split = |v: u64| -> [u64; 8] { core::array::from_fn(|i| (v >> (4 * i)) & 15) };
    let (x, y) = (0xdead_beefu64, 0x0123_4567u64);
    let honest: [(u64, u64); 8] = core::array::from_fn(|i| (split(x)[i], split(y)[i]));
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(512, 1);
    for backend in backends() {
        let run = |nib: [(u64, u64); 8]| -> Result<(R1CSProof, Vec<CompressedRistretto>, Cost), R1CSError> {
            let mut t = Transcript::new(b"xor32");
            let mut p = Prover::new(&pc, &mut t);
            p.set_backend(backend);
            let (V0, vx) = p.commit(Scalar::from(x), Scalar::from(1u64));
            let (V1, vy) = p.commit(Scalar::from(y), Scalar::from(2u64));
            let z = xor32(&mut p, vx, vy, Some(nib))?;
            let (V2, vz) = p.commit(Scalar::from(x ^ y), Scalar::from(3u64));
            p.constrain(z - vz);
            let cost = p.cost();
            Ok((p.prove_with_rng(&bp, &mut ChaCha20Rng::seed_from_u64(5))?, vec![V0, V1, V2], cost))
        };
        let verify = |proof: &R1CSProof, V: &[CompressedRistretto]| {
            let mut t = Transcript::new(b"xor32");
            let mut v = Verifier::new(&mut t);
            v.set_backend(backend);
            let (vx, vy) = (v.commit(V[0]), v.commit(V[1]));
            let z = xor32(&mut v, vx, vy, None)?;
            let vz = v.commit(V[2]);
            v.constrain(z - vz);
            v.verify(proof, &pc, &bp)
        };
        let (proof, V, cost) = run(honest).unwrap();
        verify(&proof, &V).unwrap();
        assert_eq!(cost.bppp_gates, 8, "one gate per lookup, no gate for the 256 multiplicities");
        // nibble 0 of x as 15 + 16 = 31, nibble 1 one less: the same x, not a row
        let mut cheat = honest;
        cheat[0].0 += 16;
        cheat[1].0 -= 1;
        assert!(matches!(run(cheat), Err(R1CSError::GadgetError { .. })), "{:?}", backend);
    }
}

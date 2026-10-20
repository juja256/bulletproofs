//! The example of the README section "Writing gadgets for both backends": the same gadget code
//! proven with Bulletproofs and with Bulletproofs++.

#![cfg(feature = "yoloproofs")]

use bulletproofs::r1cs::{
    Backend, CircuitBuilder, ConstraintSystem, LinearCombination, Prover, R1CSError, R1CSProof, TableId, Variable,
    Verifier,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// The public tables of the statement: created once, shared by all lookups.
struct Tables {
    /// `{0, ..., 255}`
    byte: TableId,
    /// `(a, b, a ^ b)` for nibbles `a, b`
    xor: TableId,
}

fn tables<CS: CircuitBuilder>(cs: &mut CS) -> Result<Tables, R1CSError> {
    let byte = cs.table((0..256u64).map(|x| vec![x]).collect())?;
    let xor = cs.table((0..256u64).map(|x| vec![x >> 4, x & 15, (x >> 4) ^ (x & 15)]).collect())?;
    Ok(Tables { byte, xor })
}

/// `x < 2^16`: two byte lookups. `v` is the prover's value (`None` for the verifier).
fn range16<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, x: LinearCombination, v: Option<u64>) -> Result<(), R1CSError> {
    let lo = cs.lookup_value(t.byte, v.map(|v| v & 0xff))?;
    let hi = cs.lookup_value(t.byte, v.map(|v| v >> 8))?;
    cs.constrain(x - lo - hi * Scalar::from(256u64));
    Ok(())
}

/// `z = x ^ y` for nibbles: one lookup of the tuple `(x, y, z)`. No range checks of `x`, `y`,
/// `z` are needed: the lookup proves that the tuple is a row, component by component.
fn xor4<CS: CircuitBuilder>(cs: &mut CS, t: &Tables, x: Variable, y: Variable, v: Option<(u64, u64)>) -> Result<Variable, R1CSError> {
    let z = cs.witness(v.map(|(a, b)| Scalar::from(a ^ b)))?;
    cs.lookup(t.xor, &[x.into(), y.into(), z.into()])?;
    Ok(z)
}

/// `output` is a permutation of `input` (a multiset equality): one reciprocal argument,
/// `sum 1/(X + x) - sum 1/(X + y) = 0`.
fn shuffle<CS: CircuitBuilder>(cs: &mut CS, input: &[Variable], output: &[Variable]) -> Result<(), R1CSError> {
    let arg = cs.reciprocal(1)?;
    for x in input {
        arg.add(cs, &[(*x).into()])?;
    }
    for y in output {
        arg.sub(cs, &[(*y).into()])?;
    }
    Ok(())
}

/// An upstream gadget, written against `ConstraintSystem` only: `x * y = z` for a public `z`.
fn product_is<CS: ConstraintSystem>(cs: &mut CS, x: Variable, y: Variable, z: u64) {
    let (_, _, xy) = cs.multiply(x.into(), y.into());
    cs.constrain(xy - Scalar::from(z));
}

/// The statement: the committed `a`, `b` are below `2^16`; the prover knows nibbles `p`, `q`
/// with `p ^ q = 9` and a permutation `(c, d)` of `(a, b)` with `c * d = product`.
/// `secret` is the prover's `(a, b, p, q)`.
fn statement<CS: CircuitBuilder>(cs: &mut CS, ab: [Variable; 2], product: u64, secret: Option<[u64; 4]>) -> Result<(), R1CSError> {
    let t = tables(cs)?;
    range16(cs, &t, ab[0].into(), secret.map(|s| s[0]))?;
    range16(cs, &t, ab[1].into(), secret.map(|s| s[1]))?;
    let p = cs.lookup_value(t.byte, secret.map(|s| s[2]))?;
    let q = cs.lookup_value(t.byte, secret.map(|s| s[3]))?;
    let r = xor4(cs, &t, p, q, secret.map(|s| (s[2], s[3])))?;
    cs.constrain(r - Scalar::from(9u64));
    // the permutation (b, a)
    let c = cs.witness(secret.map(|s| Scalar::from(s[1])))?;
    let d = cs.witness(secret.map(|s| Scalar::from(s[0])))?;
    shuffle(cs, &ab, &[c, d])?;
    product_is(cs, c, d, product);
    Ok(())
}

fn prove(backend: Backend, a: u64, b: u64, p: u64, q: u64, product: u64) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let pc = PedersenGens::default();
    let mut transcript = Transcript::new(b"guide");
    // public data that the constraints do not contain goes into the transcript first
    transcript.append_u64(b"product", product);
    let mut prover = Prover::new(&pc, &mut transcript);
    prover.set_backend(backend);
    let (ca, va) = prover.commit(Scalar::from(a), Scalar::from(11u64));
    let (cb, vb) = prover.commit(Scalar::from(b), Scalar::from(12u64));
    statement(&mut prover, [va, vb], product, Some([a, b, p, q]))?;
    let bp = BulletproofGens::new(prover.cost().gens_capacity(backend), 1);
    Ok((prover.prove(&bp)?, vec![ca, cb]))
}

fn verify(proof: &R1CSProof, commitments: &[CompressedRistretto], product: u64) -> Result<(), R1CSError> {
    let pc = PedersenGens::default();
    let mut transcript = Transcript::new(b"guide");
    transcript.append_u64(b"product", product);
    let mut verifier = Verifier::new(&mut transcript);
    // this verifier accepts either backend; a stricter one would require one of them
    verifier.set_backend(proof.backend());
    let ab = [verifier.commit(commitments[0]), verifier.commit(commitments[1])];
    statement(&mut verifier, ab, product, None)?;
    let bp = BulletproofGens::new(verifier.cost().gens_capacity(proof.backend()), 1);
    verifier.verify(proof, &pc, &bp)
}

fn backends() -> Vec<Backend> {
    #[allow(unused_mut)]
    let mut b = vec![Backend::Bp];
    #[cfg(feature = "bppp")]
    b.push(Backend::Bppp);
    b
}

#[test]
fn the_guide_example_proves_on_both_backends() {
    for backend in backends() {
        let (proof, cs) = prove(backend, 300, 7, 12, 5, 2100).unwrap();
        let bytes = proof.to_bytes();
        println!("{}: {} bytes", backend, bytes.len());
        verify(&R1CSProof::from_bytes(&bytes).unwrap(), &cs, 2100).unwrap();
        assert!(verify(&proof, &cs, 2101).is_err(), "another statement");
    }
}

#[test]
fn the_guide_example_rejects_false_statements() {
    for backend in backends() {
        // a = 2^16 is out of range: its high byte 256 is no row of the byte table
        assert!(prove(backend, 1 << 16, 1, 12, 5, 1 << 16).is_err(), "{}", backend);
        // 16 ^ 25 = 9, but 16 is no nibble: (16, 25, 9) is no row of the xor table
        assert!(prove(backend, 300, 7, 16, 25, 2100).is_err(), "{}", backend);
        // 12 ^ 6 = 10 != 9: the lookup holds, the linear constraint does not; the proof does
        // not verify
        let (proof, cs) = prove(backend, 300, 7, 12, 6, 2100).unwrap();
        assert!(verify(&proof, &cs, 2100).is_err(), "{}", backend);
        // a wrong product: the prover does not refuse a violated linear constraint (both
        // backends), the proof does not verify
        let (proof, cs) = prove(backend, 300, 7, 12, 5, 2101).unwrap();
        assert!(verify(&proof, &cs, 2101).is_err(), "{}", backend);
    }
}


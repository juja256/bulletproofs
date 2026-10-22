#![allow(non_snake_case)]

use super::*;
use crate::bppp::BpppGens;
use crate::curve::Secp256k1Compressed;
use crate::r1cs::{lc, Backend, ConstraintSystem, Prover, R1CSProof, Variable, Verifier};
use crate::simplicity::CompileTranscript;
use crate::{BulletproofGens, PedersenGens, Sha256Transcript};
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

type S = K;

#[test]
fn folding_and_nodes() {
    let ((), tape) = with_tape(|| {
        let w = Traced::witness(0, K::from(5u64));
        let c = Traced::constant(K::from(3u64)) * Traced::constant(K::from(4u64));
        let r = w * c + w;
        assert_eq!(r.value, K::from(65u64));
        assert!(c.node.is_none());
    });
    assert_eq!(tape.ops.len(), 3, "{:?}", tape.ops); // WitScalar, MulC, Add
}

/// `x · y = 15` with committed `x`, `y`; with `lookup` (the prover's value, `u64::MAX` for the
/// verifier), also `x` in a table of 0..16: the reciprocal form then has poles, so batch
/// inversion and `compile(eta, alpha)` run.
fn gadget<CS: ConstraintSystem<S>>(cs: &mut CS, x: Variable, y: Variable, lookup: Option<u64>) {
    let o = cs.multiply(lc(x), lc(y)).unwrap();
    cs.constrain(lc(o) - S::from(15u64));
    if let Some(xv) = lookup {
        let t = cs.table((0..16u64).map(|v| vec![v]).collect()).unwrap();
        let l = cs.lookup_value(t, if xv == u64::MAX { None } else { Some(xv) }).unwrap();
        cs.constrain(lc(l) - lc(x));
    }
}

struct Statement {
    pc: PedersenGens<Secp256k1>,
    bp: BulletproofGens<Secp256k1>,
}

impl Statement {
    fn new() -> Self {
        Statement { pc: PedersenGens::<Secp256k1>::default(), bp: BulletproofGens::<Secp256k1>::new(256, 1) }
    }

    fn prove(&self, seed: u64, lookup: bool) -> (R1CSProof<Secp256k1>, Vec<Secp256k1Compressed>) {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let mut t = Sha256Transcript::new(b"trace");
        let mut p = Prover::new(&self.pc, &mut t);
        p.set_backend(Backend::Bppp);
        let r = |rng: &mut ChaCha20Rng| <S as ff::Field>::random(rng);
        let (cx, x) = p.commit(S::from(3u64), r(&mut rng));
        let (cy, y) = p.commit(S::from(5u64), r(&mut rng));
        gadget(&mut p, x, y, lookup.then(|| 3));
        (p.prove_with_rng(&self.bp, &mut rng).unwrap(), vec![cx, cy])
    }

    /// The lowered circuit and its generators, as the verifier builds them.
    fn circuit(&self, V: &[Secp256k1Compressed], lookup: bool) -> crate::bppp::ReciprocalCircuit<S> {
        let mut ct = CompileTranscript::new(b"circuit");
        let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
        v.set_backend(Backend::Bppp);
        let x = v.commit(V[0]);
        let y = v.commit(V[1]);
        gadget(&mut v, x, y, lookup.then(|| u64::MAX));
        v.lower_builder_bppp().unwrap()
    }
}

/// The traced `reciprocal::terms` of a proof: its terms (as k256 values), the tape, the
/// proof's scalars and the challenges.
fn traced_terms(st: &Statement, proof: &R1CSProof<Secp256k1>, V: &[Secp256k1Compressed], lookup: bool) -> (crate::bppp::terms::Terms<TracedCurve>, Tape, Vec<K>) {
    let c = st.circuit(V, lookup);
    let (cp, n_lin, n_mm) = proof.bppp_parts().unwrap();
    let gens = BpppGens::new(&st.pc, &st.bp, n_lin, n_mm).unwrap();
    let ct = c.map_scalars(Traced::constant);
    let n: Vec<TracedPoint> = gens.n.iter().map(|p| TracedPoint::constant(*p)).collect();
    let tg = BpppGens::<TracedCurve> { g: TracedPoint::constant(gens.g), h: gens.h.iter().map(|p| TracedPoint::constant(*p)).collect(), n: &n };
    let bytes = cp.to_bytes();
    let wit: Vec<K> = cp.wnla.l.iter().chain(&cp.wnla.n).copied().collect();
    let (terms, tape) = with_tape(|| {
        // the order of the proof's bytes: C_L, C_R, C_O, C_S, then (X_r, R_r) per round
        let rounds = cp.wnla.X.iter().zip(&cp.wnla.R).flat_map(|(x, r)| vec![*x, *r]);
        let head = [cp.C_L, cp.C_R, cp.C_O, cp.C_S];
        let pts = head.iter().copied().chain(rounds);
        for (i, p) in pts.enumerate() {
            register_witness_point(&p, i);
        }
        for (i, s) in wit.iter().enumerate() {
            register_witness_scalar(&<K as Field>::to_bytes32(s), i);
        }
        let tp = crate::bppp::CircuitProof::<TracedCurve>::from_bytes_dims(&bytes, n_lin, n_mm).unwrap();
        let mut t = CompileTranscript::new(b"terms");
        crate::bppp::reciprocal::terms(&tp, &ct, &tg, V, &mut t).unwrap()
    });
    (terms, tape, wit)
}

#[test]
fn traced_terms_match_the_verifier() {
    let st = Statement::new();
    let (proof, V) = st.prove(1, false);
    let (traced, tape, wit) = traced_terms(&st, &proof, &V, false);
    // untraced
    let c = st.circuit(&V, false);
    let (cp, n_lin, n_mm) = proof.bppp_parts().unwrap();
    let gens = BpppGens::new(&st.pc, &st.bp, n_lin, n_mm).unwrap();
    let plain = crate::bppp::reciprocal::terms(cp, &c, &gens, &V, &mut CompileTranscript::new(b"terms")).unwrap();
    assert_eq!(traced.g.value, plain.g);
    assert_eq!(traced.h.iter().map(|x| x.value).collect::<Vec<_>>(), plain.h);
    assert_eq!(traced.n.iter().map(|x| x.value).collect::<Vec<_>>(), plain.n);
    assert_eq!(traced.points.len(), plain.points.len());
    for ((tk, tp), (pk, pp)) in traced.points.iter().zip(&plain.points) {
        assert_eq!(tk.value, *pk);
        assert_eq!(tp.value, *pp);
    }
    // the points of the proof are witness points, the commitments constants
    assert!(traced.points.iter().any(|(_, p)| matches!(p.src, PointSrc::Witness(_))));
    assert!(traced.points.iter().any(|(_, p)| p.src == PointSrc::Const));
    // the numeric model reproduces every node
    let chal: Vec<K> = {
        let mut ch = Vec::new();
        for (op, v) in tape.ops.iter().zip(&tape.values) {
            if let TOp::Challenge(k) = op {
                if ch.len() <= *k {
                    ch.resize(*k + 1, K::ZERO);
                }
                ch[*k] = *v;
            }
        }
        ch
    };
    assert_eq!(tape.eval(&wit, &chal), tape.values);
    assert!(tape.ops.iter().any(|o| matches!(o, TOp::Challenge(_))));
    assert!(tape.ops.iter().any(|o| matches!(o, TOp::WitScalar(_))));
}

#[test]
fn tapes_of_two_proofs_have_the_same_structure() {
    let st = Statement::new();
    let (p1, V1) = st.prove(1, true);
    let (p2, V2) = st.prove(2, true);
    // the commitments differ (other blindings): the circuit is the same, the statement not;
    // the structure of the verifier's computation must still be the same
    let (_, t1, _) = traced_terms(&st, &p1, &V1, true);
    let (_, t2, _) = traced_terms(&st, &p2, &V2, true);
    assert_eq!(t1.structure(), t2.structure());
    assert!(t1.ops.iter().any(|o| matches!(o, TOp::Invert(_))), "the lookup's poles invert");
}

#[test]
fn equality_of_two_nodes_is_refused() {
    let r = std::panic::catch_unwind(|| {
        with_tape(|| {
            let a = Traced::witness(0, K::from(2u64));
            let b = Traced::witness(1, K::from(2u64));
            a == b
        })
    });
    let msg = r.unwrap_err().downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default();
    assert!(msg.contains("equality of two traced values"), "{}", msg);
}

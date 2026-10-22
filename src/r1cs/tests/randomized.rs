//! Randomized constraints run on BP only: BP++ and the Simplicity compiler refuse them.

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use crate::curve::Ristretto;
use crate::r1cs::*;
use crate::{BulletproofGens, PedersenGens};

/// Randomized constraints cannot run on BP++ (the challenge would sit between `C_O` and
/// `C_R`, where right wires are unbound); both sides return a gadget error.
#[test]
fn randomized_constraints_need_bp() {
    let pc = PedersenGens::<Ristretto>::default();
    let bp = BulletproofGens::new(16, 1);
    let mut t = Transcript::new(b"rand");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (_, x) = prover.commit(Scalar::from(4u64), Scalar::from(1u64));
    prover
        .specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"z");
            let (l, _, o) = cs.multiply(x - z, x - z);
            cs.constrain(o - l * Scalar::from(2u64) + l);
            Ok(())
        })
        .unwrap();
    match prover.prove(&bp) {
        Err(R1CSError::GadgetError { .. }) => {}
        other => panic!("expected a gadget error, got {:?}", other.map(|_| ())),
    }
    // the verifier refuses too: otherwise a proof of the circuit without the randomized part
    // would pass for a statement that also has it (found in review)
    let mut t = Transcript::new(b"rand");
    let mut prover = Prover::new(&pc, &mut t);
    prover.set_backend(Backend::Bppp);
    let (vx, _) = prover.commit(Scalar::from(4u64), Scalar::from(1u64));
    let proof = prover.prove(&bp).unwrap();
    let mut t = Transcript::new(b"rand");
    let mut verifier = Verifier::new(&mut t);
    verifier.set_backend(Backend::Bppp);
    let x = verifier.commit(vx);
    verifier
        .specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"z");
            cs.constrain(x - z);
            Ok(())
        })
        .unwrap();
    match verifier.verify(&proof, &pc, &bp) {
        Err(R1CSError::GadgetError { .. }) => {}
        other => panic!("expected a gadget error, got {:?}", other),
    }
}

/// The Simplicity compiler refuses a circuit with randomized constraints.
#[cfg(feature = "simplicity")]
#[test]
fn simplicity_refuses_randomized_constraints() {
    use crate::curve::{Curve, Secp256k1};
    use crate::simplicity::{CompileTranscript, SIGHASH_LABEL};
    use crate::TranscriptBackend;
    type K = k256::Scalar;
    let pc = PedersenGens::<Secp256k1>::default();
    let bp = BulletproofGens::new(64, 1);
    let commitment = Secp256k1::compress(&pc.commit(K::from(3u64), K::from(7u64)));
    for randomized in [false, true] {
        let mut ct = CompileTranscript::new(b"test");
        ct.append_message(SIGHASH_LABEL, &[0u8; 32]);
        let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
        v.set_backend(Backend::Bppp);
        let x = v.commit(commitment);
        let o = v.multiply(lc(x), lc(x)).unwrap();
        v.constrain(lc(o) - K::from(9u64));
        if randomized {
            v.specify_randomized_constraints(move |cs| {
                let z = cs.challenge_scalar(b"z");
                let (_, _, o) = cs.multiply(lc(x) - z, lc(x));
                cs.constrain(lc(o) - lc(o));
                Ok(())
            })
            .unwrap();
        }
        assert_eq!(v.compile_to_simplicity(&pc, &bp).is_err(), randomized);
    }
}

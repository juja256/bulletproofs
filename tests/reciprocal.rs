use rand::thread_rng;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use merlin::Transcript;
use std::time::Instant;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, R1CSProof, RandomizableConstraintSystem, RandomizedConstraintSystem, Variable, Verifier};
use bulletproofs::r1cs::R1CSError;

/// Create a single-value range proof for `value` in [0, 2^nbits).
/// Returns (proof, commitment, blinding).
pub fn create_range_proof(value: u64, nbits: usize) -> (RangeProof, CompressedRistretto) {
   
    
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);
    let start = Instant::now();
    let mut transcript = Transcript::new(b"range-proof-example");
    let mut rng = thread_rng();
    let blinding = Scalar::random(&mut rng);

    let (proof, committed) = RangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut transcript,
        value,
        &blinding,
        nbits,
    )
    .expect("failed to create range proof");

    let elapsed = start.elapsed();
    println!("create_range_proof execution time: {:.2?}, size = {}", elapsed, proof.to_bytes().len());
    
    (proof, committed)
}

/// Verify a single-value range proof.
pub fn verify_range_proof(proof: &RangeProof, commitment: &CompressedRistretto, nbits: usize) -> bool {
    
    
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);
    let start = Instant::now();
    let mut transcript = Transcript::new(b"range-proof-example");

    let result = proof
        .verify_single(&bp_gens, &pc_gens, &mut transcript, commitment, nbits)
        .is_ok();

    let elapsed = start.elapsed();
    println!("verify_range_proof execution time: {:.2?}", elapsed);
    
    result
}

/// Create multiple range proofs for a vector of values.
pub fn create_multiple_range_proofs(values: &[u64], nbits: usize) -> (RangeProof, Vec<CompressedRistretto>) {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, values.len());
    let start = Instant::now();
    let mut transcript = Transcript::new(b"range-proof-example");
    let mut rng = thread_rng();
    
    let blindings: Vec<Scalar> = (0..values.len())
        .map(|_| Scalar::random(&mut rng))
        .collect();

    let (proof, commitments) = RangeProof::prove_multiple(
        &bp_gens,
        &pc_gens,
        &mut transcript,
        values,
        &blindings,
        nbits,
    )
    .expect("failed to create range proofs");

    let elapsed = start.elapsed();
    println!("create_multiple_range_proofs execution time: {:.2?}, size = {}", elapsed, proof.to_bytes().len());
    
    (proof, commitments)
}

/// Verify multiple range proofs.
pub fn verify_multiple_range_proofs(proof: &RangeProof, commitments: &[CompressedRistretto], nbits: usize) -> bool {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, commitments.len());

    let start = Instant::now();
    let mut transcript = Transcript::new(b"range-proof-example");

    let result = proof
        .verify_multiple(&bp_gens, &pc_gens, &mut transcript, commitments, nbits)
        .is_ok();

    let elapsed = start.elapsed();
    println!("verify_multiple_range_proofs execution time: {:.2?}", elapsed);
    
    result
}

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = Scalar::ONE;
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - 1u64));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

/// Create a range proof using the R1CS API. Returns (proof, commitment, blinding).
pub fn create_range_proof_r1cs(value: u64, nbits: usize) -> (R1CSProof, CompressedRistretto) {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);

    let start = Instant::now();
    let mut transcript = Transcript::new(b"r1cs-range-proof");
    let mut rng = thread_rng();
    let blinding = Scalar::random(&mut rng);

    // Create prover, commit the value, and run the gadget to add constraints.
    let mut prover = Prover::new(&pc_gens, &mut transcript);
    // `commit` returns a (Variable, CompressedRistretto) tuple in this API.
    let (commitment, var_v) = prover.commit(Scalar::from(value), blinding);

    range_proof_gadget(&mut prover, var_v.into(), Some(value), nbits)
        .expect("range_proof_gadget failed in prover");

    let proof = prover.prove(&bp_gens).expect("prover failed to create proof");

    let elapsed = start.elapsed();
    println!("create_range_proof_r1cs execution time: {:.2?}", elapsed);

    (proof, commitment)
}

/// Verify an R1CS range proof produced by `create_range_proof_r1cs`.
pub fn verify_range_proof_r1cs(proof: &R1CSProof, commitment: &CompressedRistretto, nbits: usize) -> bool {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);

    let start = Instant::now();
    let mut transcript = Transcript::new(b"r1cs-range-proof");

    // Create verifier, re-create committed variable, and run the same gadget (no assignment).
    let mut verifier = Verifier::new(&mut transcript);
    let var_v = verifier.commit(*commitment);

    if let Err(_) = range_proof_gadget(&mut verifier, var_v.into(), None, nbits) {
        return false;
    }

    let result = verifier
        .verify(proof, &pc_gens, &bp_gens)
        .is_ok();

    let elapsed = start.elapsed();
    println!("verify_range_proof_r1cs execution time: {:.2?}", elapsed);

    result
}

pub fn get_multiplicities(v: u64, b: usize) -> Vec<u64> {
    let n = 64; // assuming 64-bit values
    let mut multiplicities = vec![0; 1 << b];
    for i in 0..(n / b) {
        let digit = (v >> (i * b)) & ((1u64 << b) - 1);
        multiplicities[digit as usize] += 1;
    }
    multiplicities
}

/// Enforces that the quantity of v is in the range [0, 2^n) using the reciprocal argument.
pub fn range_proof_reciprocal_gadget<CS: RandomizableConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_assignment: Option<u64>,
    n: usize,
    b: usize, // 2^b is the size of lookup table
) -> Result<(), R1CSError> {
     let multiplicities = v_assignment
            .map(|val| get_multiplicities(val, b));

    let m_assignments: Vec<Option<u64>> = (0..(1<<b))
        .map(|i| multiplicities.as_ref().map(|vec| vec[i]))
        .collect(); // multiplicity assignments
    
    let m_vars: Vec<Variable> = m_assignments.iter()
        .map(|&assign| {
            cs.allocate(assign.map(|v| Scalar::from(v)))
        })
        .collect::<Result<Vec<Variable>, R1CSError>>()?; // commit to multiplicities

    let d_vars = (0..(n / b)).map(|i| {
        cs.allocate(v_assignment.map(|q| {
            Scalar::from((q >> (i*b)) & ((1u64 << b) - 1))
        }))
    }).collect::<Result<Vec<Variable>, R1CSError>>()?; // commit to digits

    cs.specify_randomized_constraints(move |cs| {
        let c = cs.challenge_scalar(b"challenge"); // get phase2 Fiat-Shamir challenge from the CS
        let mut exp_2b = Scalar::ONE;
        let mut sum_reciprocals = LinearCombination::from(Scalar::ZERO);
       
        let sum_m = m_vars.iter().enumerate()
            .fold(LinearCombination::from(Scalar::ZERO), |acc, (i, &var)| {
                acc + var * (Scalar::from(i as u64) + c).invert()
            }); // Sum(m_i / (c + i), i = 0..2^b-1)

        for i in 0..n/b {
            let (r, d_plus_c, o) = cs.allocate_multiplier(v_assignment.map(|q| {
                let d: u64 = (q >> (i*b)) & ((1u64 << b) - 1); // extract digit value
                let r = (Scalar::from(d) + c).invert(); // compute reciprocal with challenge
                (r, c + Scalar::from(d)) // r*(c+d) = 1
            }))?;

            // enforce that d_plus_c is constructed correctly
            cs.constrain(d_plus_c - c - d_vars[i]);

            // Enforce the product to be 1 to assure reciprocity
            cs.constrain(o - Scalar::ONE);

            // Add `-d_i*2^i` to the linear combination
            // in order to form the following constraint by the end of the loop:
            // v = Sum(d_i * 2^{b*i}, i = 0..n/b-1)
            v = v - (d_plus_c - c) * exp_2b;
            exp_2b = (0..b).fold(exp_2b, |acc, _| acc + acc); // exp_2 *= 2^b
            sum_reciprocals = sum_reciprocals + r;
        }

        // Enforce that v = Sum(d_i * 2^{b*i}, i = 0..n/b-1)
        cs.constrain(v);
        // Enforce that Sum(m_i / (c + i), i = 0..2^b-1) = Sum(1 / (c + d_i), i = 0..n/b-1) -- core of the reciprocal argument
        cs.constrain(sum_m - sum_reciprocals);
        
        Ok(())
    })
}

/// Create an R1CS range proof using the reciprocal gadget with b = 4.
/// Returns (proof, commitment, blinding).
pub fn create_range_proof_reciprocal(value: u64, nbits: usize) -> (R1CSProof, CompressedRistretto) {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(32, 1);

    let start = Instant::now();
    let mut transcript = Transcript::new(b"r1cs-range-proof-reciprocal");
    let mut rng = thread_rng();
    let blinding = Scalar::random(&mut rng);

    // Create prover, commit the value, and run the reciprocal gadget to add constraints.
    let mut prover = Prover::new(&pc_gens, &mut transcript);
    let (commitment, var_v) = prover.commit(Scalar::from(value), blinding);

    // use b = 4
    range_proof_reciprocal_gadget(&mut prover, var_v.into(), Some(value), nbits, 4)
        .expect("range_proof_reciprocal_gadget failed in prover");

    let proof = prover.prove(&bp_gens).expect("prover failed to create proof");

    let elapsed = start.elapsed();
    println!("create_range_proof_reciprocal execution time: {:.2?}, size = {}", elapsed, proof.to_bytes().len());

    (proof, commitment)
}

/// Verify an R1CS range proof produced by `create_range_proof_reciprocal` (b = 4).
pub fn verify_range_proof_reciprocal(proof: &R1CSProof, commitment: &CompressedRistretto, nbits: usize) -> bool {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(32, 1);

    let start = Instant::now();
    let mut transcript = Transcript::new(b"r1cs-range-proof-reciprocal");

    // Create verifier, re-create committed variable, and run the same reciprocal gadget (no assignment).
    let mut verifier = Verifier::new(&mut transcript);
    let var_v = verifier.commit(*commitment);

    if let Err(_) = range_proof_reciprocal_gadget(&mut verifier, var_v.into(), None, nbits, 4) {
        return false;
    }

    let result = verifier
        .verify(proof, &pc_gens, &bp_gens)
        .is_ok();

    let elapsed = start.elapsed();
    println!("verify_range_proof_reciprocal execution time: {:.2?}", elapsed);

    result
}

mod tests {
    use super::*;
    #[test]
    fn test_create_and_verify_r1cs_range_proof() {
        let value = 42u64;
        let (proof, commit) = create_range_proof_r1cs(value, 64);
        assert!(verify_range_proof_r1cs(&proof, &commit, 64));
    }

    #[test]
    fn test_create_and_verify_multiple_range_proofs() {
        let values = vec![10u64, 20u64, 30u64, 50u64];
        let (proof, commits) = create_multiple_range_proofs(&values, 64);
        assert!(verify_multiple_range_proofs(&proof, &commits, 64));
    }

    #[test]
    fn test_create_and_verify_range_proof() {
        let (proof, commit) = create_range_proof(42u64, 64);
        assert!(verify_range_proof(&proof, &commit, 64));
    }

    #[test]
    fn test_create_and_verify_r1cs_range_proof_reciprocal() {
        let value = 42u64;
        let (proof, commit) = create_range_proof_reciprocal(value, 64);
        assert!(verify_range_proof_reciprocal(&proof, &commit, 64));
    }
}

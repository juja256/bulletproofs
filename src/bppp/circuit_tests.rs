//! Tests of `bppp::circuit`.

use super::*;
#[allow(unused_imports)]
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
#[allow(unused_imports)]
use curve25519_dalek::scalar::Scalar;
use crate::bppp::testutil::{sc, scs, slot, sparse_from, ScalarRng};
use crate::bppp::transcript::Replay;
use crate::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;

struct Shape {
    n_m: usize,
    n_o: usize,
    n_v: usize,
    n_lin: usize,
    k: usize,
    n_l: usize,
    f_l: bool,
    f_m: bool,
    spread: bool,
}

fn rand_vec(rng: &mut ChaCha20Rng, n: usize) -> Vec<Scalar> {
    (0..n).map(|_| Scalar::random(rng)).collect()
}

fn sparse(rng: &mut ChaCha20Rng, rows: usize, cols: usize) -> SparseMatrix {
    use rand_chacha::rand_core::RngCore;
    let mut m = SparseMatrix::new(cols);
    for _ in 0..rows {
        let mut terms = Vec::new();
        for c in 0..cols {
            if rng.next_u32() % 2 == 0 {
                terms.push((c, Scalar::random(rng)));
            }
        }
        m.push_row(terms);
    }
    m
}

/// A random circuit with a satisfying witness: `W_l`, `W_m` and the witness are random,
/// `a_l` and `a_m` are chosen to satisfy the circuit.
fn instance(rng: &mut ChaCha20Rng, s: &Shape) -> (ArithmeticCircuit, CircuitWitness) {
    let n_w = 2 * s.n_m + s.n_o;
    let w = CircuitWitness {
        w_l: rand_vec(rng, s.n_m),
        w_r: rand_vec(rng, s.n_m),
        w_o: rand_vec(rng, s.n_o),
        v: (0..s.k).map(|_| rand_vec(rng, s.n_v)).collect(),
        s: rand_vec(rng, s.k),
    };
    let w_l = sparse(rng, s.n_l, n_w);
    let w_m = sparse(rng, s.n_m, n_w);
    let full: Vec<Scalar> = w.w_l.iter().chain(&w.w_r).chain(&w.w_o).copied().collect();
    let w_v: Vec<Scalar> = w.v.iter().flatten().copied().collect();
    let pad = |r: usize| w_v.get(r).copied().unwrap_or(Scalar::ZERO);
    let flag = |f: bool| if f { Scalar::ONE } else { Scalar::ZERO };
    let a_l = w_l.mul_vec(&full).iter().enumerate().map(|(r, x)| -(x + flag(s.f_l) * pad(r))).collect();
    let a_m = w_m
        .mul_vec(&full)
        .iter()
        .enumerate()
        .map(|(r, x)| w.w_l[r] * w.w_r[r] - x - flag(s.f_m) * pad(r))
        .collect();
    let slots = [Slot::NormO, Slot::LinO, Slot::LinL, Slot::LinR];
    let partition =
        (0..s.n_o).map(|i| if s.spread { (slots[i % 4], i / 4) } else { (Slot::NormO, i) }).collect();
    let c = ArithmeticCircuit {
        n_m: s.n_m,
        n_o: s.n_o,
        n_v: s.n_v,
        n_lin: s.n_lin,
        k: s.k,
        w_l,
        a_l,
        w_m,
        a_m,
        f_l: s.f_l,
        f_m: s.f_m,
        partition,
    };
    (c, w)
}

fn shapes() -> Vec<Shape> {
    let mut out = Vec::new();
    for &(f_l, f_m) in &[(false, false), (true, false), (false, true), (true, true)] {
        for &k in &[1, 3] {
            // inputs need a flag that puts them into constraints
            let k = if f_l || f_m { k } else { 0 };
            for &n_v in &[1, 4] {
                for &spread in &[false, true] {
                    out.push(Shape {
                        n_m: 16,
                        n_o: 8,
                        n_v,
                        n_lin: (n_v - 1).max(4),
                        k,
                        n_l: (k * n_v).max(5) + 2,
                        f_l,
                        f_m,
                        spread,
                    });
                }
            }
        }
    }
    out.push(Shape { n_m: 1, n_o: 0, n_v: 1, n_lin: 0, k: 1, n_l: 1, f_l: true, f_m: true, spread: false });
    out.push(Shape { n_m: 5, n_o: 3, n_v: 3, n_lin: 2, k: 1, n_l: 4, f_l: true, f_m: false, spread: false });
    out
}

fn gens_for(c: &ArithmeticCircuit) -> (PedersenGens, BulletproofGens) {
    (PedersenGens::default(), BulletproofGens::new(c.gens_capacity(), 1))
}

fn commitments(g: &BpppGens, w: &CircuitWitness) -> Vec<CompressedRistretto> {
    w.v.iter().zip(&w.s).map(|(v, s)| g.commit_input(v, *s).compress()).collect()
}

/// The prover without its satisfiability check, to test what the verifier rejects.
fn prove_unchecked<C: Curve, T: BpppTranscript + ?Sized, R: RngCore + CryptoRng>(
    c: &ArithmeticCircuit<C::Scalar>,
    g: &BpppGens<C>,
    V: &[C::Compressed],
    w: &CircuitWitness<C::Scalar>,
    t: &mut T,
    rng: &mut R,
) -> Result<CircuitProof<C>, ProofError> {
    prove_impl(c, g, V, w, t, |_, _| rng, false)
}

fn prove_and_verify(c: &ArithmeticCircuit, w: &CircuitWitness, rng: &mut ChaCha20Rng) -> Result<(), ProofError> {
    let (pc, bp) = gens_for(c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m)?;
    let V = commitments(&g, w);
    let proof = prove_unchecked(c, &g, &V, w, &mut Transcript::new(b"test"), rng)?;
    let parsed = CircuitProof::<Ristretto>::from_bytes(&proof.to_bytes(), c)?;
    assert_eq!(parsed, proof);
    proof.verify(c, &g, &V, &mut Transcript::new(b"test"))
}

/// The prover reproduces the independent Python reference (`ref/bppp_ref.py`,
/// `tests/vectors/bppp/circuit.json`) given its randomness and challenges, and the
/// verifier accepts exactly the satisfied cases.
fn reference_vectors<C: Curve>()
where
    C::Scalar: crate::bppp::testutil::TestScalar,
{
    let file = crate::bppp::testutil::vectors::<C>(
        include_str!("../../tests/vectors/bppp/circuit.json"),
        include_str!("../../tests/vectors/bppp/secp256k1/circuit.json"),
    );
    let pc = PedersenGens::<C>::for_curve();
    for case in file["cases"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let u = |k: &str| case[k].as_u64().unwrap() as usize;
        let (n_m, n_o, n_lin) = (u("n_m"), u("n_o"), u("n_lin"));
        let n_w = 2 * n_m + n_o;
        let c = ArithmeticCircuit::<C::Scalar> {
            n_m,
            n_o,
            n_v: u("n_v"),
            n_lin,
            k: u("k"),
            w_l: sparse_from(&case["w_l"], n_w),
            a_l: scs(&case["a_l"]),
            w_m: sparse_from(&case["w_m"], n_w),
            a_m: scs(&case["a_m"]),
            f_l: u("f_l") == 1,
            f_m: u("f_m") == 1,
            partition: case["partition"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| (slot(p[0].as_str().unwrap()), p[1].as_u64().unwrap() as usize))
                .collect(),
        };
        assert_eq!(c.n_l(), u("n_l"), "{}", name);
        let w = CircuitWitness {
            w_l: scs(&case["w_L"]),
            w_r: scs(&case["w_R"]),
            w_o: scs(&case["w_O"]),
            v: case["v"].as_array().unwrap().iter().map(scs).collect(),
            s: scs(&case["s"]),
        };
        assert_eq!(c.is_satisfied(&w), case["satisfied"].as_bool().unwrap(), "{}", name);
        let bp = BulletproofGens::<C>::for_curve(crate::bppp::gens::capacity(n_lin, n_m), 1);
        let g = BpppGens::new(&pc, &bp, n_lin, n_m).unwrap();
        let point = |p: &serde_json::Value| crate::bppp::testutil::sym_point::<C>(p, &g.g, &g.h, g.n);
        let V: Vec<C::Compressed> = w.v.iter().zip(&w.s).map(|(v, s)| C::compress(&g.commit_input(v, *s))).collect();
        for (i, p) in case["V"].as_array().unwrap().iter().enumerate() {
            assert_eq!(V[i], point(p), "{}: V_{}", name, i);
        }
        let r = &case["rand"];
        let randomness: Vec<C::Scalar> =
            ["r_O", "r_L", "r_R", "l_S", "n_S"].iter().flat_map(|k| scs(&r[*k])).collect();
        let ch = &case["chal"];
        let challenges: Vec<C::Scalar> = ["rho", "lambda", "beta", "delta", "tau"]
            .iter()
            .map(|k| sc(&ch[*k]))
            .chain(scs(&case["gammas"]))
            .collect();
        let proof = prove_unchecked(&c, &g, &V, &w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness))
            .unwrap();
        let checked = prove(&c, &g, &V, &w, &mut Replay::new(challenges.clone()), &mut ScalarRng::new(&randomness));
        assert_eq!(checked.is_ok(), case["satisfied"].as_bool().unwrap(), "{}: prover check", name);
        assert_eq!(proof.C_L, point(&case["C_L"]), "{}: C_L", name);
        assert_eq!(proof.C_R, point(&case["C_R"]), "{}: C_R", name);
        assert_eq!(proof.C_O, point(&case["C_O"]), "{}: C_O", name);
        assert_eq!(proof.C_S, point(&case["C_S"]), "{}: C_S", name);
        let rounds = case["rounds"].as_array().unwrap();
        assert_eq!(proof.wnla.X.len(), rounds.len(), "{}: rounds", name);
        for (i, round) in rounds.iter().enumerate() {
            assert_eq!(proof.wnla.X[i], point(&round["X"]), "{}: X_{}", name, i);
            assert_eq!(proof.wnla.R[i], point(&round["R"]), "{}: R_{}", name, i);
        }
        assert_eq!(proof.wnla.l, scs::<C::Scalar>(&case["l_final"]), "{}: l", name);
        assert_eq!(proof.wnla.n, scs::<C::Scalar>(&case["n_final"]), "{}: n", name);
        let verdict = proof.verify(&c, &g, &V, &mut Replay::new(challenges)).is_ok();
        assert_eq!(verdict, case["verifies"].as_bool().unwrap(), "{}: verdict", name);
    }
}

#[test]
fn matches_reference_vectors() {
    reference_vectors::<Ristretto>();
}

#[test]
fn matches_reference_vectors_secp256k1() {
    reference_vectors::<crate::curve::Secp256k1>();
}

#[test]
fn honest_proofs_verify() {
    let mut rng = ChaCha20Rng::seed_from_u64(10);
    for s in shapes() {
        let (c, w) = instance(&mut rng, &s);
        assert!(c.is_satisfied(&w));
        let res = prove_and_verify(&c, &w, &mut rng);
        assert!(res.is_ok(), "f_l={} f_m={} k={} n_v={} spread={}: {:?}", s.f_l, s.f_m, s.k, s.n_v, s.spread, res);
    }
}

/// Each kind of violated constraint makes the proof fail: a linear one, a multiplicative
/// one, and one through an input value.
#[test]
fn unsatisfied_witnesses_are_rejected() {
    let mut rng = ChaCha20Rng::seed_from_u64(11);
    for s in shapes().into_iter().filter(|s| s.n_m > 1) {
        for tamper in 0..6 {
            let (mut c, mut w) = instance(&mut rng, &s);
            match tamper {
                0 => c.a_l[0] += Scalar::ONE,
                1 => *c.a_m.last_mut().unwrap() += Scalar::ONE,
                2 => w.w_l[0] += Scalar::ONE,
                3 => *c.a_l.last_mut().unwrap() += Scalar::ONE,
                4 => c.a_m[s.n_m / 2] += Scalar::ONE,
                _ if s.k > 0 => *w.v[s.k - 1].last_mut().unwrap() += Scalar::ONE,
                _ => continue,
            }
            if c.is_satisfied(&w) {
                continue; // the tampered entry happened to be unconstrained
            }
            assert!(prove_and_verify(&c, &w, &mut rng).is_err(), "tamper {} accepted", tamper);
        }
    }
}

#[test]
fn scalar_inputs_are_pedersen_commitments() {
    let pc = PedersenGens::default();
    let bp = BulletproofGens::new(16, 1);
    let g = BpppGens::new(&pc, &bp, 3, 16).unwrap();
    let (v, s) = (Scalar::from(1234u64), Scalar::from(99u64));
    assert_eq!(g.commit_input(&[v], s), pc.commit(v, s));
}

/// The transcript carries the dimensions, the circuit digest, the inputs and every
/// commitment before the challenges that depend on them; the verifier absorbs the same.
#[test]
fn transcript_binds_messages() {
    let mut rng = ChaCha20Rng::seed_from_u64(12);
    let s = Shape { n_m: 4, n_o: 2, n_v: 2, n_lin: 2, k: 2, n_l: 5, f_l: true, f_m: true, spread: true };
    let (c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    let chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
    let mut t = Replay::new(chal.clone());
    let proof = prove(&c, &g, &V, &w, &mut t, &mut rng).unwrap();
    let u = |x: u64| x.to_le_bytes().to_vec();
    let mut expected: Vec<(&[u8], Vec<u8>)> = vec![
        (b"bppp-circuit v1", vec![]),
        (b"N_m", u(4)),
        (b"N_O", u(2)),
        (b"N_v", u(2)),
        (b"N_lin", u(2)),
        (b"k", u(2)),
        (b"N_l", u(5)),
        (b"f_l", u(1)),
        (b"f_m", u(1)),
        (b"G", g.g.compress().as_bytes().to_vec()),
        (b"H_0", g.h[0].compress().as_bytes().to_vec()),
        (b"circuit", c.digest().to_vec()),
        (b"V", V[0].as_bytes().to_vec()),
        (b"V", V[1].as_bytes().to_vec()),
        (b"C_L", proof.C_L.as_bytes().to_vec()),
        (b"C_R", proof.C_R.as_bytes().to_vec()),
        (b"C_O", proof.C_O.as_bytes().to_vec()),
        (b"rho", vec![]),
        (b"lambda", vec![]),
        (b"beta", vec![]),
        (b"delta", vec![]),
        (b"C_S", proof.C_S.as_bytes().to_vec()),
        (b"tau", vec![]),
    ];
    let header = expected.len();
    assert_eq!(&t.log[..header], &expected[..], "prover");
    assert_eq!(t.log[header].0, &b"bppp-wnla v1"[..]);
    expected = t.log.clone();
    let mut tv = Replay::new(chal);
    proof.verify(&c, &g, &V, &mut tv).unwrap();
    assert_eq!(tv.log, expected, "verifier");
}

#[test]
fn digest_changes_with_every_part_of_the_circuit() {
    let mut rng = ChaCha20Rng::seed_from_u64(13);
    let s = Shape { n_m: 4, n_o: 4, n_v: 2, n_lin: 2, k: 1, n_l: 3, f_l: true, f_m: false, spread: true };
    let (c, _) = instance(&mut rng, &s);
    let d = c.digest();
    let mut variants = Vec::new();
    let mut x = c.clone();
    x.a_l[1] += Scalar::ONE;
    variants.push(x);
    let mut x = c.clone();
    x.a_m[0] += Scalar::ONE;
    variants.push(x);
    let mut x = c.clone();
    x.f_m = true;
    variants.push(x);
    let mut x = c.clone();
    x.partition.swap(0, 1);
    variants.push(x);
    let mut x = c.clone();
    x.w_l.push_row(vec![(0, Scalar::ONE)]);
    x.a_l.push(Scalar::ZERO);
    variants.push(x);
    for v in variants {
        assert_ne!(v.digest(), d);
    }
}

/// The value generator is part of the statement: a prover who picks `G` after seeing the
/// challenges (solving the verification equation for it) must fail. Found in review.
#[test]
fn forged_value_generator_is_rejected() {
    let mut rng = ChaCha20Rng::seed_from_u64(79);
    let s = Shape { n_m: 4, n_o: 2, n_v: 1, n_lin: 2, k: 1, n_l: 3, f_l: true, f_m: false, spread: false };
    let (mut c, w) = instance(&mut rng, &s);
    c.a_l[1] += Scalar::ONE;
    assert!(!c.is_satisfied(&w));
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    let proof = prove_unchecked(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).unwrap();
    assert!(proof.verify(&c, &g, &V, &mut Transcript::new(b"t")).is_err());
    // Replay the verifier: A is the coefficient of G in the check, B the rest; G := -B/A.
    let mut t = Transcript::new(b"t");
    absorb_statement(&mut t, &c, &g, &V);
    t.append_point(b"C_L", &proof.C_L);
    t.append_point(b"C_R", &proof.C_R);
    t.append_point(b"C_O", &proof.C_O);
    let (rho, lambda): (Scalar, Scalar) = (t.challenge(b"rho"), t.challenge(b"lambda"));
    let (beta, delta): (Scalar, Scalar) = (t.challenge(b"beta"), t.challenge(b"delta"));
    let wt = Weights::new(&c, rho, lambda);
    let delta_inv = delta.invert();
    t.append_point(b"C_S", &proof.C_S);
    let tau: Scalar = t.challenge(b"tau");
    let (tau_inv, tau3) = (tau.invert(), tau * tau * tau);
    let p_n = wt.p_n(delta_inv).eval(tau, tau_inv, c.n_m);
    let p_s = p_n.iter().zip(&wt.mu_vec).map(|(a, m)| a * a * m).sum::<Scalar>() + tau3 * wt.affine;
    let cvec: Vec<Scalar> = c_r(beta, tau, tau_inv).chain(wt.c_l(delta_inv).eval(tau, tau_inv, c.n_lin)).collect();
    let sc = proof.wnla.verification_scalars(&cvec, rho, c.n_m, &mut t).unwrap();
    let d = |p: &CompressedRistretto| p.decompress().unwrap();
    let mut B = -(d(&proof.C_S) * tau_inv) - d(&proof.C_O) * delta - d(&proof.C_L) * tau - d(&proof.C_R) * (tau * tau);
    for (nu, v) in wt.nu.iter().zip(&V) {
        B -= d(v) * (tau3 * nu);
    }
    for (gm, (x, r)) in sc.gammas.iter().zip(proof.wnla.X.iter().zip(&proof.wnla.R)) {
        B -= d(x) * gm + d(r) * (gm * gm - Scalar::ONE);
    }
    for (s_, h) in sc.h.iter().zip(&g.h) {
        B += h * s_;
    }
    for ((s_, p), n) in sc.n.iter().zip(&p_n).zip(g.n.iter()) {
        B += n * (s_ - p);
    }
    let forged = BpppGens { g: -(B * (sc.g - p_s).invert()), h: g.h.clone(), n: g.n };
    assert!(proof.verify(&c, &forged, &V, &mut Transcript::new(b"t")).is_err());
}

/// Inputs that enter no constraint (`k > 0` with neither flag) would be accepted
/// unchecked; such circuits are rejected. Found in review.
#[test]
fn unused_inputs_are_rejected() {
    let mut rng = ChaCha20Rng::seed_from_u64(16);
    let s = Shape { n_m: 4, n_o: 2, n_v: 1, n_lin: 1, k: 1, n_l: 2, f_l: false, f_m: false, spread: false };
    let (c, _) = instance(&mut rng, &s);
    assert!(c.check().is_err());
    let s0 = Shape { k: 0, ..s };
    assert!(instance(&mut rng, &s0).0.check().is_ok());
}

/// The prover checks the value term and refuses an unsatisfied witness instead of
/// producing a proof that cannot verify.
#[test]
fn prover_refuses_unsatisfied_witness() {
    let mut rng = ChaCha20Rng::seed_from_u64(17);
    let s = Shape { n_m: 4, n_o: 2, n_v: 2, n_lin: 2, k: 1, n_l: 3, f_l: true, f_m: true, spread: true };
    let (mut c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    assert!(prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).is_ok());
    c.a_m[2] += Scalar::ONE;
    assert!(prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).is_err());
}

/// Absurd dimensions from the caller are errors, not panics or huge allocations.
#[test]
fn absurd_dimensions_are_errors() {
    let mut rng = ChaCha20Rng::seed_from_u64(18);
    let s = Shape { n_m: 4, n_o: 2, n_v: 1, n_lin: 1, k: 1, n_l: 2, f_l: true, f_m: false, spread: false };
    let (c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    let proof = prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).unwrap();
    for (n_lin, n_m) in [(usize::MAX / 2, 4), (usize::MAX - 3, 4), (1, usize::MAX / 2)] {
        let mut big = c.clone();
        big.n_lin = n_lin;
        big.n_m = n_m;
        let _ = big.check(); // must not panic or allocate per slot
        assert!(proof.verify(&big, &g, &V, &mut Transcript::new(b"t")).is_err());
        assert!(prove(&big, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).is_err());
        assert!(CircuitProof::<Ristretto>::from_bytes(&proof.to_bytes(), &big).is_err());
    }
    assert!(WnlaProof::<Ristretto>::from_bytes(&[], usize::MAX, 0).is_err());
    assert!(WnlaProof::<Ristretto>::from_bytes(&[], usize::MAX, usize::MAX).is_err());
}

#[test]
fn degenerate_challenges_fail() {
    let mut rng = ChaCha20Rng::seed_from_u64(14);
    let s = Shape { n_m: 4, n_o: 2, n_v: 1, n_lin: 1, k: 1, n_l: 2, f_l: true, f_m: false, spread: false };
    let (c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    // challenge order: rho, lambda, beta, delta, tau, gammas...
    for zero in [0usize, 2, 3, 4] {
        let mut chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
        chal[zero] = Scalar::ZERO;
        assert!(prove(&c, &g, &V, &w, &mut Replay::new(chal), &mut rng).is_err(), "challenge {} zero", zero);
    }
    let good: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
    let proof = prove(&c, &g, &V, &w, &mut Replay::new(good.clone()), &mut rng).unwrap();
    proof.verify(&c, &g, &V, &mut Replay::new(good)).unwrap();
    for zero in [0usize, 2, 3, 4] {
        let mut chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
        chal[zero] = Scalar::ZERO;
        assert!(proof.verify(&c, &g, &V, &mut Replay::new(chal)).is_err(), "challenge {} zero", zero);
    }
}

/// Challenges that may be zero (lambda, the norm argument's gamma): honest proofs still
/// verify (spec §3.4); rho, beta, delta, tau are checked above. The verifier rejects a zero
/// rho/beta/delta/tau before looking at the proof, so no proof crafted for it can pass.
#[test]
fn zero_lambda_and_gamma_are_complete() {
    let mut rng = ChaCha20Rng::seed_from_u64(16);
    let s = Shape { n_m: 8, n_o: 3, n_v: 2, n_lin: 2, k: 2, n_l: 5, f_l: true, f_m: true, spread: false };
    let (c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    for zero in [1usize, 5, 6, 7] {
        let mut chal: Vec<Scalar> = (2..20u64).map(Scalar::from).collect();
        chal[zero] = Scalar::ZERO;
        let proof = prove(&c, &g, &V, &w, &mut Replay::new(chal.clone()), &mut rng).unwrap();
        proof.verify(&c, &g, &V, &mut Replay::new(chal)).unwrap_or_else(|e| panic!("challenge {}: {:?}", zero, e));
    }
}

#[test]
fn malformed_inputs_are_errors() {
    let mut rng = ChaCha20Rng::seed_from_u64(15);
    let s = Shape { n_m: 4, n_o: 2, n_v: 2, n_lin: 2, k: 2, n_l: 5, f_l: true, f_m: false, spread: true };
    let (c, w) = instance(&mut rng, &s);
    let (pc, bp) = gens_for(&c);
    let g = BpppGens::new(&pc, &bp, c.n_lin, c.n_m).unwrap();
    let V = commitments(&g, &w);
    let proof = prove(&c, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).unwrap();
    let bytes = proof.to_bytes();
    assert!(CircuitProof::<Ristretto>::from_bytes(&bytes[1..], &c).is_err());
    assert!(CircuitProof::<Ristretto>::from_bytes(&[], &c).is_err());
    let ok = |p: &CircuitProof, V: &[CompressedRistretto]| p.verify(&c, &g, V, &mut Transcript::new(b"t")).is_ok();
    assert!(ok(&proof, &V));
    assert!(!ok(&proof, &V[..1]), "missing input");
    let mut swapped = V.clone();
    swapped.swap(0, 1);
    assert!(!ok(&proof, &swapped), "inputs swapped");
    let mut bad = proof.clone();
    bad.C_S = CompressedRistretto([0xff; 32]);
    assert!(!ok(&bad, &V), "invalid point");
    let mut bad = proof.clone();
    bad.C_O = proof.C_L;
    assert!(!ok(&bad, &V), "C_O replaced");
    // shape errors are errors, not panics
    let mut c2 = c.clone();
    c2.partition.push((Slot::NormO, 0));
    assert!(prove(&c2, &g, &V, &w, &mut Transcript::new(b"t"), &mut rng).is_err());
    let mut c3 = c.clone();
    c3.partition[0] = c3.partition[1];
    assert!(c3.check().is_err(), "partition not injective");
    let small = BulletproofGens::new(2, 1);
    assert!(BpppGens::new(&pc, &small, c.n_lin, c.n_m).is_err());
}

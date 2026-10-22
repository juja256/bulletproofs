//! Compiling a lowered circuit into its Simplicity verifier: trace the BP++ verifier on a dummy
//! proof of the circuit's dimensions, lower the transcript log, the tape and the final
//! multiscalar multiplication into the IR, and keep what the witness of a real proof needs.

#![allow(non_snake_case)]

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use k256::elliptic_curve::ff::{Field as _, PrimeField as _};
use k256::elliptic_curve::sec1::ToEncodedPoint;

use crate::bppp::{BpppGens, BpppTranscript, CircuitProof, ReciprocalCircuit};
use crate::curve::{Curve, Field, PointEncoding, Secp256k1, Secp256k1Compressed};
use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::R1CSProof;
use crate::simplicity::ir::{Op, Options, Prog, Ty, Val};
use crate::simplicity::point::{assert_infinity, const_gej, const_gej_compressed, ge_to_gej, msm, witness_point, witness_scalar, WitPoint};
use crate::simplicity::run::{bit_value, execute_term, weight_of, word_value, Env, ExecError, Report, MAX_CELLS};
use crate::simplicity::term::Term;
use crate::simplicity::sha::{lower_log, ChallengeVals, Part, Rec};
use crate::simplicity::trace::{register_witness_point, register_witness_scalar, with_tape, NodeId, PointSrc, TOp, Tape, Traced, TracedCurve, TracedPoint};
use crate::simplicity::CompileTranscript;

type K = k256::Scalar;

impl core::fmt::Debug for SimplicityVerifier {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SimplicityVerifier").field("cmr", &self.cmr).field("stats", &self.stats).finish()
    }
}

/// A Simplicity program that verifies the BP++ proofs of one circuit, bound to the spending
/// transaction (`jet_sig_all_hash` in the transcript).
#[derive(Clone)]
pub struct SimplicityVerifier {
    term: Term,
    /// The program's text, written on first use (an artifact).
    text: std::sync::OnceLock<String>,
    cmr: ::simplicity::Cmr,
    n_lin: usize,
    n_mm: usize,
    stats: Stats,
}

/// The witness of a proof: its points (as parity and x) and scalars, by witness name.
#[derive(Clone, Debug)]
pub struct SimplicityWitness(HashMap<Arc<str>, ::simplicity::Value>);

/// What the program contains.
#[derive(Clone, Debug)]
pub struct Stats {
    /// Jet calls by name, as executed (a recomputed value counts at each reader).
    pub jets: BTreeMap<&'static str, usize>,
    /// Live operations of the traced verifier.
    pub tape_ops: usize,
    /// Terms of the final multiscalar multiplication.
    pub msm_terms: usize,
    /// Points of the proof (witness values).
    pub witness_points: usize,
    /// Scalars of the proof (witness values).
    pub witness_scalars: usize,
    /// Steps the program runs (stored values, values read by nobody, checks).
    pub steps: usize,
    /// Steps that store a value for later steps (the rest is recomputed where it is read).
    pub stored: usize,
    /// Σ over steps of the bits kept for later steps (the scheduler's measure of copying).
    pub live_bits: u64,
    /// The lowering the compiler chose (the lightest; the CMR depends on it).
    pub lowering: String,
}

fn gadget_err(s: &str) -> R1CSError {
    R1CSError::GadgetError { description: s.into() }
}

impl SimplicityVerifier {
    /// The program's commitment Merkle root.
    pub fn cmr(&self) -> ::simplicity::Cmr {
        self.cmr
    }

    /// The program in Simplicity's human-readable encoding.
    pub fn to_text(&self) -> &str {
        self.text.get_or_init(|| self.term.text().expect("the program types"))
    }

    /// What the program contains.
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// The witness for `proof`: an error for a proof of other dimensions, with a point that is
    /// not on the curve or is the identity (the program cannot take it), or of the BP backend.
    pub fn witness(&self, proof: &R1CSProof<Secp256k1>) -> Result<SimplicityWitness, R1CSError> {
        let (cp, n_lin, n_mm) = proof.bppp_parts().ok_or_else(|| gadget_err("not a BP++ proof"))?;
        if (n_lin, n_mm) != (self.n_lin, self.n_mm) {
            return Err(gadget_err("a proof of other dimensions"));
        }
        let scalars: Vec<K> = cp.wnla.l.iter().chain(&cp.wnla.n).copied().collect();
        Ok(SimplicityWitness(witness_map(&proof_points(cp), &scalars)?))
    }

    /// Run the program with `w` in the transaction `env`, as a node would.
    pub fn execute(&self, w: &SimplicityWitness, env: &Env) -> Result<Report, ExecError> {
        execute_term(&self.term, &w.0, env, true)
    }
}

/// The witness of a proof's points (as parity and x) and final scalars, by witness name.
fn witness_map(points: &[Secp256k1Compressed], scalars: &[K]) -> Result<HashMap<Arc<str>, ::simplicity::Value>, R1CSError> {
    let mut w = HashMap::new();
    for (i, c) in points.iter().enumerate() {
        let pt = Secp256k1::decompress(c).ok_or(R1CSError::VerificationError)?;
        let e = pt.to_affine().to_encoded_point(false);
        let (x, y) = match (e.x(), e.y()) {
            (Some(x), Some(y)) => (x.to_vec(), y.to_vec()),
            _ => return Err(gadget_err("the identity in a proof (not supported by the program)")),
        };
        w.insert(Arc::from(format!("p{}", i)), ::simplicity::Value::product(bit_value(y[31] & 1 == 1), word_value(&x)));
    }
    for (i, s) in scalars.iter().enumerate() {
        w.insert(Arc::from(format!("s{}", i)), word_value(&s.to_repr()));
    }
    Ok(w)
}

/// The proof's points in the order of its bytes: `C_L, C_R, C_O, C_S`, then `(X_r, R_r)` per round.
fn proof_points<C: Curve>(cp: &CircuitProof<C>) -> Vec<C::Compressed> {
    let mut v = vec![cp.C_L, cp.C_R, cp.C_O, cp.C_S];
    for (x, r) in cp.wnla.X.iter().zip(&cp.wnla.R) {
        v.push(*x);
        v.push(*r);
    }
    v
}

/// A dummy proof of the circuit's dimensions: random points (multiples of `G`) and scalars.
/// Random, so that no statement can be crafted to equal one of its points or scalars (the
/// tracer tells proof data from constants by their bytes); the program does not depend on it.
pub(crate) fn dummy_proof<R: rand_core::RngCore + rand_core::CryptoRng>(c: &ReciprocalCircuit<K>, rng: &mut R) -> (Vec<Secp256k1Compressed>, Vec<K>) {
    let (n_lin, n_mm) = (c.n_lin, c.n_p + c.n_m);
    let (k, af, bf) = crate::bppp::wnla::rounds(n_lin + crate::bppp::gens::H_FIXED, n_mm);
    let points = (0..4 + 2 * k).map(|_| Secp256k1::compress(&(k256::ProjectivePoint::GENERATOR * K::random(&mut *rng)))).collect();
    let scalars = (0..af + bf).map(|_| K::random(&mut *rng)).collect();
    (points, scalars)
}

#[cfg(test)]
thread_local! {
    /// Tests: compile with these generators (compressed or not) and options only.
    pub(crate) static FORCE: std::cell::RefCell<Option<(bool, Options)>> = const { std::cell::RefCell::new(None) };
}

/// Threads compiling a program ([`set_compile_threads`]).
static COMPILE_THREADS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(4);

/// Threads the compiler weighs its candidate programs on: 4 by default, 0 for every core. Each
/// holds one candidate (fib from bpvm: about 0.7 GB), so more threads trade memory for time:
/// fib compiles in 26 s on 1 thread, 10 s on 4 (3.4 GB), 7 s on 8 or more (6 to 7.5 GB). The
/// program does not depend on it.
pub fn set_compile_threads(n: usize) {
    COMPILE_THREADS.store(n, std::sync::atomic::Ordering::Relaxed);
}

/// `f` on every item, on up to [`set_compile_threads`] threads (a scoped pool taking items in turn); the results in
/// the items' order.
fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let threads = match COMPILE_THREADS.load(std::sync::atomic::Ordering::Relaxed) {
        0 => cores,
        n => n.min(cores),
    }
    .min(items.len())
    .max(1);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::Mutex<Option<R>>> = items.iter().map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= items.len() {
                    break;
                }
                let r = f(&items[i]);
                *slots[i].lock().expect("a result slot") = Some(r);
            });
        }
    });
    slots.into_iter().map(|m| m.into_inner().expect("a result slot").expect("every item mapped")).collect()
}

/// The lowerings the compiler tries; it keeps the lightest program (ties to the first).
const LOWERINGS: [Options; 6] = [
    Options { role_passes: 1, hot_cold: false, small_words: false, shared_funcs: false },
    Options { role_passes: 2, hot_cold: false, small_words: false, shared_funcs: false },
    Options { role_passes: 3, hot_cold: false, small_words: false, shared_funcs: false },
    Options { role_passes: 1, hot_cold: true, small_words: false, shared_funcs: false },
    Options { role_passes: 2, hot_cold: true, small_words: false, shared_funcs: false },
    Options { role_passes: 3, hot_cold: true, small_words: false, shared_funcs: false },
];

/// The transcript domain of R1CS proofs on the BP++ backend (as `Verifier::verify_bppp`).
const BPPP_DOMAIN: &[u8] = b"bppp-r1cs v2";

/// Compile the lowered circuit `c` with statement `V`, whose verifier transcript so far is `t`.
pub(crate) fn compile(
    c: &ReciprocalCircuit<K>,
    V: &[Secp256k1Compressed],
    t: &CompileTranscript,
    pc: &PedersenGens<Secp256k1>,
    bp: &BulletproofGens<Secp256k1>,
) -> Result<SimplicityVerifier, R1CSError> {
    compile_with(c, V, t, pc, bp, &mut rand::rngs::OsRng)
}

/// [`compile`] with the randomness of the dummy proof.
pub(crate) fn compile_with<R: rand_core::RngCore + rand_core::CryptoRng>(
    c: &ReciprocalCircuit<K>,
    V: &[Secp256k1Compressed],
    t: &CompileTranscript,
    pc: &PedersenGens<Secp256k1>,
    bp: &BulletproofGens<Secp256k1>,
    rng: &mut R,
) -> Result<SimplicityVerifier, R1CSError> {
    if !t.log().iter().any(|r| matches!(r, Rec::Bytes(ps) if ps.contains(&Part::Sighash))) {
        return Err(gadget_err("the transcript has no sighash record (SIGHASH_LABEL)"));
    }
    let (n_lin, n_mm) = (c.n_lin, c.n_p + c.n_m);
    let gens = BpppGens::new(pc, bp, n_lin, n_mm).map_err(|_| R1CSError::InvalidGeneratorsLength)?;
    let proof = DummyProof::new(c, V, &gens, rng)?;
    let tr = trace(c, V, t, &gens, &proof)?;

    // the program with the generators as constant points and as x and parity (`compressed`),
    // built on all cores; then the lightest lowering of either
    #[cfg(test)]
    let forced = FORCE.with(|f| *f.borrow());
    #[cfg(not(test))]
    let forced: Option<(bool, Options)> = None;
    let modes: Vec<bool> = match forced {
        Some((c, _)) => vec![c],
        None => vec![false, true],
    };
    let progs: Vec<(Prog, usize)> = par_map(&modes, |c| build(&tr, &proof, &gens, *c));
    #[cfg(test)]
    if let Some(k) = modes.iter().position(|c| !*c) {
        LAST_STORED.with(|s| *s.borrow_mut() = Some(progs[k].0.stored_report()));
    }
    let dummy = witness_map(&proof.points, &proof.scalars)?;
    let (weight, k, opts) = lightest_lowering(&progs, &dummy, forced.map(|f| f.1))?;
    let (compressed, msm_count) = (modes[k], progs[k].1);
    let low = progs[k].0.lower(&opts);
    // lowering is deterministic: the winner lowered again is the program that was weighed
    debug_assert_eq!(weight_of(&low.term, &dummy).ok().map(|w| w.0), Some(weight), "the winner lowered again differs");
    let term = low.term;
    let commit = term.commit().map_err(|e| gadget_err(&format!("the generated program does not type: {}", e)))?;
    let cmr = commit.cmr();
    let lowering = format!(
        "generators {}, role passes {}, hot/cold {}, small words {}, shared functions {}",
        if compressed { "x and parity" } else { "points" },
        opts.role_passes,
        opts.hot_cold,
        opts.small_words,
        opts.shared_funcs
    );
    let stats = Stats {
        jets: low.jets,
        tape_ops: tr.live.iter().filter(|x| **x).count(),
        msm_terms: msm_count,
        witness_points: proof.points.len(),
        witness_scalars: proof.scalars.len(),
        steps: low.steps,
        stored: low.stored,
        live_bits: low.live_bits,
        lowering,
    };
    Ok(SimplicityVerifier { term, text: std::sync::OnceLock::new(), cmr, n_lin, n_mm, stats })
}

/// A random proof of the circuit's dimensions, on which the verifier is traced: its points,
/// scalars and encoding.
struct DummyProof {
    points: Vec<Secp256k1Compressed>,
    scalars: Vec<K>,
    bytes: Vec<u8>,
}

impl DummyProof {
    fn new<R: rand_core::RngCore + rand_core::CryptoRng>(c: &ReciprocalCircuit<K>, V: &[Secp256k1Compressed], gens: &BpppGens<Secp256k1>, rng: &mut R) -> Result<Self, R1CSError> {
        let (points, scalars) = dummy_proof(c, rng);
        // a constant point equal to a point of the proof would be taken for proof data
        // (negligible for random points unless crafted for them)
        let constants = V.iter().copied().chain(std::iter::once(gens.g).chain(gens.h.iter().copied()).chain(gens.n.iter().copied()).map(|p| Secp256k1::compress(&p)));
        for k in constants {
            if points.contains(&k) {
                return Err(gadget_err("a statement point equals a point of the dummy proof"));
            }
        }
        let mut bytes = Vec::new();
        for p in &points {
            bytes.extend_from_slice(p.as_bytes());
        }
        for s in &scalars {
            bytes.extend_from_slice(&s.to_repr());
        }
        Ok(DummyProof { points, scalars, bytes })
    }
}

/// The traced verifier: the scalars of its final multiscalar multiplication, its transcript
/// log, and the tape with its live nodes.
struct Trace {
    terms: crate::bppp::terms::Terms<TracedCurve>,
    log: Vec<Rec>,
    tape: Tape,
    live: Vec<bool>,
}

/// Run the verifier of `c` on the dummy proof with traced values.
fn trace(c: &ReciprocalCircuit<K>, V: &[Secp256k1Compressed], t: &CompileTranscript, gens: &BpppGens<Secp256k1>, proof: &DummyProof) -> Result<Trace, R1CSError> {
    let ct = c.map_scalars(Traced::constant);
    let n: Vec<TracedPoint> = gens.n.iter().map(|p| TracedPoint::constant(*p)).collect();
    let tg = BpppGens::<TracedCurve> { g: TracedPoint::constant(gens.g), h: gens.h.iter().map(|p| TracedPoint::constant(*p)).collect(), n: &n };
    let mut tt = t.clone();
    let run = || {
        with_tape(|| {
            for (i, p) in proof.points.iter().enumerate() {
                register_witness_point(p, i);
            }
            for (i, s) in proof.scalars.iter().enumerate() {
                register_witness_scalar(&<K as Field>::to_bytes32(s), i);
            }
            let tp = CircuitProof::<TracedCurve>::from_bytes_dims(&proof.bytes, c.n_lin, c.n_p + c.n_m)?;
            BpppTranscript::domain_sep(&mut tt, BPPP_DOMAIN);
            let terms = crate::bppp::reciprocal::terms(&tp, &ct, &tg, V, &mut tt)?;
            Ok::<_, crate::errors::ProofError>((terms, tt.log().to_vec()))
        })
    };
    let ((terms, log), tape) = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)) {
        Ok((Ok(x), tape)) => (x, tape),
        Ok((Err(e), _)) => return Err(gadget_err(&format!("tracing the verifier failed: {:?}", e))),
        Err(e) => {
            let msg = e.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| e.downcast_ref::<String>().cloned()).unwrap_or_default();
            return Err(gadget_err(&format!("the verifier is not traceable: {}", msg)));
        }
    };
    let roots: Vec<NodeId> = std::iter::once(&terms.g)
        .chain(&terms.h)
        .chain(&terms.n)
        .chain(terms.points.iter().map(|(k, _)| k))
        .filter_map(|t| t.node)
        .collect();
    let live = tape.live(&roots);
    #[cfg(test)]
    LAST_TAPE_KINDS.with(|k| {
        let mut m = std::collections::BTreeMap::new();
        for (i, op) in tape.ops.iter().enumerate() {
            if live[i] {
                let name = format!("{:?}", op);
                *m.entry(name.split('(').next().unwrap().to_string()).or_insert(0usize) += 1;
            }
        }
        *k.borrow_mut() = Some(m);
    });
    Ok(Trace { terms, log, tape, live })
}

/// The program of the traced verifier, with the generators as constant points or
/// (`compressed`) as x and parity decompressed by the program; and its number of terms in the
/// final sum.
fn build(tr: &Trace, proof: &DummyProof, gens: &BpppGens<Secp256k1>, compressed: bool) -> (Prog, usize) {
    let mut p = Prog::new();
    let wp: Vec<WitPoint> = (0..proof.points.len()).map(|i| witness_point(&mut p, &format!("p{}", i))).collect();
    let ws: Vec<Val> = (0..proof.scalars.len()).map(|i| witness_scalar(&mut p, &format!("s{}", i))).collect();
    let mut lw = TapeLowering { tape: &tr.tape, live: &tr.live, vals: HashMap::new(), ws: &ws };
    let challenges = {
        let mut parts = |p: &mut Prog, part: &Part, ch: &[ChallengeVals]| match part {
            Part::Sighash => vec![(p.push(Op::Jet("sig_all_hash", vec![], Ty::word())), 32)],
            Part::WitPoint(i) => vec![(wp[*i].sec1_prefix, 1), (wp[*i].x, 32)],
            Part::Scalar(n) => vec![(lw.node(p, NodeId(*n), ch), 32)],
            Part::Const(_) => unreachable!("constants are hashed by lower_log"),
        };
        lower_log(&mut p, &tr.log, usize::MAX, &mut parts)
    };
    // every live node (the checks among them), in tape order
    for i in 0..tr.tape.ops.len() {
        if tr.live[i] {
            lw.node(&mut p, NodeId(i as u32), &challenges);
        }
    }
    let scalar = |p: &mut Prog, lw: &mut TapeLowering, t: &Traced| -> Option<Val> {
        match t.node {
            Some(n) => Some(lw.node(p, n, &challenges)),
            None if bool::from(t.value.is_zero()) => None,
            None => Some(p.push(Op::Const(Ty::word(), t.value.to_repr().to_vec()))),
        }
    };
    let constant = |p: &mut Prog, pt: &k256::AffinePoint| if compressed { const_gej_compressed(p, pt) } else { const_gej(p, pt) };
    let terms = &tr.terms;
    let mut msm_terms = Vec::new();
    let generators = std::iter::once((&terms.g, gens.g)).chain(terms.h.iter().zip(gens.h.iter().copied())).chain(terms.n.iter().zip(gens.n.iter().copied()));
    for (k, pt) in generators {
        if let Some(kv) = scalar(&mut p, &mut lw, k) {
            let g = constant(&mut p, &pt.to_affine());
            msm_terms.push((kv, g));
        }
    }
    for (k, pt) in &terms.points {
        // a constant identity (a commitment to zero with a zero blinding) adds nothing
        if pt.src == PointSrc::Const && bool::from(group::Group::is_identity(&pt.value)) {
            continue;
        }
        if let Some(kv) = scalar(&mut p, &mut lw, k) {
            let g = match pt.src {
                PointSrc::Witness(i) => ge_to_gej(&mut p, wp[i].ge),
                PointSrc::Const => constant(&mut p, &pt.value.to_affine()),
            };
            msm_terms.push((kv, g));
        }
    }
    let acc = msm(&mut p, &msm_terms);
    assert_infinity(&mut p, acc);
    let p = crate::simplicity::opt::optimize(&p);
    debug_assert!(p.unread_witnesses().is_empty(), "witnesses nobody reads: {:?}", p.unread_witnesses());
    (p, msm_terms.len())
}

/// The lightest lowering of the programs `progs` (generator modes): (weight, index of the
/// program, options). Weights come from the dummy proof's witness (the same types, so the same
/// bytes and cost). The candidates are weighed on all cores, a worker returning only a weight;
/// the choice is the sequential one, the first lightest in a fixed order, so the CMR does not
/// depend on the threads. A candidate that needs more cells than consensus allows is never
/// kept. `forced` (tests) weighs one lowering only.
fn lightest_lowering(progs: &[(Prog, usize)], dummy: &HashMap<Arc<str>, ::simplicity::Value>, forced: Option<Options>) -> Result<(u64, usize, Options), R1CSError> {
    let weigh = |k: usize, opts: &Options| -> Result<Option<u64>, R1CSError> {
        let l = progs[k].0.lower(opts);
        let (w, cells) = weight_of(&l.term, dummy).map_err(|e| gadget_err(&format!("the generated program does not type: {:?}", e)))?;
        Ok((cells <= MAX_CELLS).then_some(w))
    };
    // the first lightest of `cands` (index of the program, options), in their order
    let lightest = |cands: &[(usize, Options)], weights: &[Option<u64>]| -> Option<(u64, usize, Options)> {
        let mut best: Option<(u64, usize, Options)> = None;
        for (&(k, o), w) in cands.iter().zip(weights) {
            if let Some(w) = *w {
                if best.map_or(true, |(b, ..)| w < b) {
                    best = Some((w, k, o));
                }
            }
        }
        best
    };
    let cands: Vec<(usize, Options)> = match forced {
        Some(o) => vec![(0, o)],
        None => (0..progs.len()).flat_map(|k| LOWERINGS.iter().map(move |o| (k, *o))).collect(),
    };
    let weights = par_map(&cands, |(k, o)| weigh(*k, o)).into_iter().collect::<Result<Vec<_>, _>>()?;
    // each generator mode's best, then small constant words and shared functions on it (they
    // trade a little cost for bytes)
    let mut per_mode: Vec<Option<(u64, usize, Options)>> = (0..progs.len())
        .map(|k| {
            let idx: Vec<usize> = (0..cands.len()).filter(|i| cands[*i].0 == k).collect();
            lightest(&idx.iter().map(|i| cands[*i]).collect::<Vec<_>>(), &idx.iter().map(|i| weights[*i]).collect::<Vec<_>>())
        })
        .collect();
    if forced.is_none() {
        let alts: Vec<(usize, Options)> = per_mode
            .iter()
            .flatten()
            .flat_map(|&(_, k, o)| [Options { small_words: true, ..o }, Options { shared_funcs: true, ..o }, Options { small_words: true, shared_funcs: true, ..o }].map(|a| (k, a)))
            .collect();
        let alt_weights = par_map(&alts, |(k, o)| weigh(*k, o)).into_iter().collect::<Result<Vec<_>, _>>()?;
        for m in per_mode.iter_mut().flatten() {
            let mut cands = vec![(m.1, m.2)];
            let mut ws = vec![Some(m.0)];
            for (i, a) in alts.iter().enumerate().filter(|(_, a)| a.0 == m.1) {
                cands.push(*a);
                ws.push(alt_weights[i]);
            }
            *m = lightest(&cands, &ws).expect("the mode's best");
        }
    }
    lightest(&per_mode.iter().flatten().map(|&(_, k, o)| (k, o)).collect::<Vec<_>>(), &per_mode.iter().flatten().map(|&(w, ..)| Some(w)).collect::<Vec<_>>())
        .ok_or_else(|| gadget_err("no program within the cell limit"))
}

#[cfg(test)]
thread_local! {
    /// Diagnostic: stored values by operation (count, bits × steps, executions), of the last compile.
    pub(crate) static LAST_STORED: std::cell::RefCell<Option<std::collections::BTreeMap<String, (usize, u64, u64)>>> = std::cell::RefCell::new(None);
}

#[cfg(test)]
thread_local! {
    /// Diagnostic: live tape operations by kind, of the last compile.
    pub(crate) static LAST_TAPE_KINDS: std::cell::RefCell<Option<std::collections::BTreeMap<String, usize>>> = std::cell::RefCell::new(None);
}

/// Tape nodes as IR values, lowered on demand (a node's arguments come before it).
struct TapeLowering<'a> {
    tape: &'a Tape,
    live: &'a [bool],
    vals: HashMap<NodeId, Val>,
    ws: &'a [Val],
}

impl<'a> TapeLowering<'a> {
    fn node(&mut self, p: &mut Prog, n: NodeId, ch: &[ChallengeVals]) -> Val {
        if let Some(v) = self.vals.get(&n) {
            return *v;
        }
        debug_assert!(self.live[n.0 as usize]);
        let op = self.tape.ops[n.0 as usize];
        for a in op.args() {
            self.node(p, a, ch);
        }
        let g = |s: &Self, a: NodeId| s.vals[&a];
        let w = Ty::word();
        let konst = |p: &mut Prog, c: &crate::simplicity::trace::ScalarBytes| p.push(Op::Const(Ty::word(), c.0.to_vec()));
        let v = match op {
            TOp::WitScalar(i) => self.ws[i],
            TOp::Challenge(k) => ch.get(k).and_then(|c| c.scalar).expect("a challenge lowered before its use"),
            TOp::Add(a, b) => p.push(Op::Jet("scalar_add", vec![g(self, a), g(self, b)], w)),
            TOp::Sub(a, b) => {
                let nb = p.push(Op::Jet("scalar_negate", vec![g(self, b)], w.clone()));
                p.push(Op::Jet("scalar_add", vec![g(self, a), nb], w))
            }
            TOp::Mul(a, b) => p.push(Op::Jet("scalar_multiply", vec![g(self, a), g(self, b)], w)),
            TOp::Neg(a) => p.push(Op::Jet("scalar_negate", vec![g(self, a)], w)),
            TOp::Invert(a) => p.push(Op::Jet("scalar_invert", vec![g(self, a)], w)),
            TOp::AddC(a, c) => {
                let k = konst(p, &c);
                p.push(Op::Jet("scalar_add", vec![g(self, a), k], w))
            }
            TOp::MulC(a, c) => {
                let k = konst(p, &c);
                p.push(Op::Jet("scalar_multiply", vec![g(self, a), k], w))
            }
            TOp::AssertNonzero(a) => {
                let z = p.push(Op::Jet("scalar_is_zero", vec![g(self, a)], Ty::Bit));
                let nz = p.push(Op::Jet("complement_1", vec![z], Ty::Bit));
                p.push(Op::Assert(nz));
                g(self, a)
            }
            TOp::AssertEq(a, c) => {
                let k = konst(p, &c);
                let e = p.push(Op::Jet("eq_256", vec![g(self, a), k], Ty::Bit));
                p.push(Op::Assert(e));
                g(self, a)
            }
            TOp::AssertNe(a, c) => {
                let k = konst(p, &c);
                let e = p.push(Op::Jet("eq_256", vec![g(self, a), k], Ty::Bit));
                let ne = p.push(Op::Jet("complement_1", vec![e], Ty::Bit));
                p.push(Op::Assert(ne));
                g(self, a)
            }
        };
        self.vals.insert(n, v);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::{lc, Backend, ConstraintSystem, Prover, Variable, Verifier};
    use crate::simplicity::run::{dummy_env, sighash_of};
    use crate::simplicity::SIGHASH_LABEL;
    use crate::{Sha256Transcript, TranscriptBackend};

    use rand_chacha::rand_core::SeedableRng;

    fn product<CS: ConstraintSystem<K>>(cs: &mut CS, x: Variable, y: Variable) {
        let o = cs.multiply(lc(x), lc(y)).unwrap();
        cs.constrain(lc(o) - K::from(15u64));
    }

    fn gens() -> (PedersenGens<Secp256k1>, BulletproofGens<Secp256k1>) {
        (PedersenGens::default(), BulletproofGens::new(64, 1))
    }

    /// The circuit and the compile transcript for statement `V`.
    fn lowered(V: &[Secp256k1Compressed]) -> (ReciprocalCircuit<K>, CompileTranscript) {
        let mut ct = CompileTranscript::new(b"test");
        TranscriptBackend::append_message(&mut ct, SIGHASH_LABEL, &[0u8; 32]);
        let c = {
            let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
            v.set_backend(Backend::Bppp);
            let (x, y) = (v.commit(V[0]), v.commit(V[1]));
            product(&mut v, x, y);
            v.lower_builder_bppp().unwrap()
        };
        (c, ct)
    }

    /// A statement point equal to a point of the dummy proof would be taken for a witness
    /// point (provenance is by bytes): the compiler refuses it.
    #[test]
    fn statement_point_equal_to_a_dummy_point_is_refused() {
        let (pc, bp) = gens();
        let seed = 9;
        let (c0, _) = lowered(&[Secp256k1::compress(&k256::ProjectivePoint::GENERATOR), Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)]);
        let (points, _) = dummy_proof(&c0, &mut rand_chacha::ChaCha20Rng::seed_from_u64(seed));
        let V = [points[0], Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)];
        let (c, ct) = lowered(&V);
        let r = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(seed));
        assert!(r.is_err(), "a statement point equal to a dummy point compiled");
    }

    /// The dummy proof is random, the program is not.
    #[test]
    fn program_does_not_depend_on_the_dummy_proof() {
        let (pc, bp) = gens();
        let g = Secp256k1::compress(&(k256::ProjectivePoint::GENERATOR * K::from(5u64)));
        let V = [g, Secp256k1::compress(&k256::ProjectivePoint::GENERATOR)];
        let (c, ct) = lowered(&V);
        let a = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(1)).unwrap();
        let b = compile_with(&c, &V, &ct, &pc, &bp, &mut rand_chacha::ChaCha20Rng::seed_from_u64(2)).unwrap();
        assert_eq!(a.to_text(), b.to_text());
    }

    /// The program's own checks, not the witness builder's: a point not on the curve and a
    /// scalar not below the group order make it fail.
    #[test]
    fn program_rejects_bad_witness_values() {
        let env = dummy_env();
        let (pc, bp) = gens();
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let mut t = Sha256Transcript::new(b"test");
        t.append_message(SIGHASH_LABEL, &sighash_of(&env));
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(Backend::Bppp);
        let (cx, x) = p.commit(K::from(3u64), K::random(&mut rng));
        let (cy, y) = p.commit(K::from(5u64), K::random(&mut rng));
        product(&mut p, x, y);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
        let V = [cx, cy];
        let (c, ct) = lowered(&V);
        let sv = compile(&c, &V, &ct, &pc, &bp).unwrap();
        let w = sv.witness(&proof).unwrap();
        assert!(sv.execute(&w, &env).is_ok());
        // x = 0 is on no point of secp256k1
        let mut bad = w.clone();
        bad.0.insert(Arc::from("p0"), ::simplicity::Value::product(bit_value(false), word_value(&[0u8; 32])));
        assert!(sv.execute(&bad, &env).is_err());
        // the group order itself
        let n = [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf,
            0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41,
        ];
        let mut bad = w.clone();
        bad.0.insert(Arc::from("s0"), word_value(&n));
        assert!(sv.execute(&bad, &env).is_err());
    }

    /// Diagnostic (`-- --ignored --nocapture`): what a small program is made of (reads of
    /// stored values and their depth, constant bytes).
    #[test]
    #[ignore]
    fn program_composition() {
        let env = dummy_env();
        let (pc, bp) = gens();
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let mut t = Sha256Transcript::new(b"test");
        t.append_message(SIGHASH_LABEL, &sighash_of(&env));
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(Backend::Bppp);
        let (cx, x) = p.commit(K::from(3u64), K::random(&mut rng));
        let (cy, y) = p.commit(K::from(5u64), K::random(&mut rng));
        product(&mut p, x, y);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
        let V = [cx, cy];
        let (c, ct) = lowered(&V);
        crate::simplicity::ir::PATH_STATS.with(|c| *c.borrow_mut() = (0, 0));
        let sv = compile(&c, &V, &ct, &pc, &bp).unwrap();
        let (reads, depth) = crate::simplicity::ir::PATH_STATS.with(|c| *c.borrow());
        let r = sv.execute(&sv.witness(&proof).unwrap(), &env).unwrap();
        let text = sv.to_text();
        let consts: usize = text.lines().filter(|l| l.contains("const 0x")).map(|l| l.split("const 0x").skip(1).map(|h| h.split(|c: char| !c.is_ascii_hexdigit()).next().unwrap().len() / 2).sum::<usize>()).sum();
        let witness_cmrs = text.matches("witness").count();
        println!("program {} B, steps {}, reads {} (mean depth {:.1}), constant bytes {}, text lines {}, witness nodes {}", r.program_bytes, sv.stats().steps, reads, depth as f64 / reads as f64, consts, text.lines().count(), witness_cmrs);
    }


    /// Diagnostic: chains of multiplications — steps, the scheduler's live bits, the cost.
    #[test]
    #[ignore]
    fn chain_growth() {
        let env = dummy_env();
        for n in [2usize, 16, 32, 64] {
            let pc = PedersenGens::<Secp256k1>::default();
            let bp = BulletproofGens::<Secp256k1>::new(2 * n + 64, 1);
            let chain = |cs: &mut dyn FnMut(crate::r1cs::LinearCombination<K>, crate::r1cs::LinearCombination<K>) -> Variable, x: Variable| {
                let mut v = lc(x);
                for _ in 0..n {
                    let o = cs(v, lc(x));
                    v = lc(o);
                }
                v
            };
            let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(1);
            let mut t = Sha256Transcript::new(b"chain");
            t.append_message(SIGHASH_LABEL, &sighash_of(&env));
            let mut p = Prover::new(&pc, &mut t);
            p.set_backend(Backend::Bppp);
            let (cx, x) = p.commit(K::from(3u64), K::random(&mut rng));
            let _ = chain(&mut |a, b| p.multiply(a, b).unwrap(), x);
            let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
            let mut ct = CompileTranscript::new(b"chain");
            TranscriptBackend::append_message(&mut ct, SIGHASH_LABEL, &[0u8; 32]);
            let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
            v.set_backend(Backend::Bppp);
            let xv = v.commit(cx);
            let _ = chain(&mut |a, b| v.multiply(a, b).unwrap(), xv);
            crate::simplicity::ir::PATH_STATS.with(|c| *c.borrow_mut() = (0, 0));
            let sv = v.compile_to_simplicity(&pc, &bp).unwrap();
            let (reads, depth) = crate::simplicity::ir::PATH_STATS.with(|c| *c.borrow());
            let r = crate::simplicity::run::execute_term(&sv.term, &sv.witness(&proof).unwrap().0, &env, false);
            let st = sv.stats();
            if let Some(kinds) = crate::simplicity::compile::LAST_TAPE_KINDS.with(|k| k.borrow().clone()) {
                println!("n {}: tape kinds {:?}", n, kinds);
            }
            if let Some(st) = crate::simplicity::compile::LAST_STORED.with(|k| k.borrow().clone()) {
                for (k, (c, bs, e)) in st {
                    println!("    stored {:>28}: {:>4} values, {:>9} bit-steps, {:>5} reads", k, c, bs, e);
                }
            }
            if let Some(b) = crate::simplicity::run::LAST_BREAKDOWN.with(|b| b.borrow().clone()) {
                for (k, c) in b.iter().filter(|(k, _)| k.starts_with('#')) {
                    println!("    {:>24} {:>10}", k, c);
                }
                let b: std::collections::BTreeMap<_, _> = b.into_iter().filter(|(k, _)| !k.starts_with('#')).collect();
                let total: u64 = b.values().sum();
                println!("n {}: breakdown total {}", n, total);
                let mut v: Vec<_> = b.into_iter().collect();
                v.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
                for (k, c) in v {
                    println!("    {:>24} {:>10} {:5.1}%", k, c, 100.0 * c as f64 / total as f64);
                }
            }
            println!("n {}: steps {}, live bits {} ({:.0} per step), reads {} depth sum {} (~{} mWU of path overhead), cost {:?}", n, st.steps, st.live_bits, st.live_bits as f64 / st.steps as f64, reads, depth, 100 * (depth + reads), r.map(|r| (r.cost_mwu, r.program_bytes, r.witness_bytes, r.cells)));
        }
    }


    // ---- every lowering the compiler may pick, on real verifiers (from the stage 4 review) ----
    fn all_opts() -> Vec<(bool, Options)> {
        let mut v = Vec::new();
        for compressed in [false, true] {
            for role_passes in 1..=3 {
                for hot_cold in [false, true] {
                    for small_words in [false, true] {
                        for shared_funcs in [false, true] {
                            v.push((compressed, Options { role_passes, hot_cold, small_words, shared_funcs }));
                        }
                    }
                }
            }
        }
        v
    }

    enum Circ { Product, Chain(usize), Table(u64, u64) }

    fn circuit<CS: crate::r1cs::ConstraintSystem<K>>(cs: &mut CS, c: &Circ, xs: &[Variable], prover: bool) {
        match c {
            Circ::Product => product(cs, xs[0], xs[1]),
            Circ::Chain(n) => {
                let mut last = K::from(3u64);
                let mut v = lc(xs[0]);
                for _ in 0..*n {
                    let o = cs.multiply(v, lc(xs[0])).unwrap();
                    v = lc(o);
                    last *= K::from(3u64);
                }
                cs.constrain(v - last);
            }
            Circ::Table(rows, lookups) => {
                let t = cs.table((0..*rows).map(|v| vec![v]).collect()).unwrap();
                for i in 0..*lookups {
                    cs.lookup_value(t, if prover { Some((i * 7) % rows) } else { None }).unwrap();
                }
                product(cs, xs[0], xs[1]);
            }
        }
    }

    fn compile_circ(c: &Circ, env: &crate::simplicity::run::Env) -> (R1CSProof<Secp256k1>, Box<dyn Fn() -> SimplicityVerifier>) {
        let n = match c { Circ::Chain(n) => *n, Circ::Table(r, _) => 4 * *r as usize, _ => 0 };
        let pc = PedersenGens::<Secp256k1>::default();
        let bp = BulletproofGens::<Secp256k1>::new(2 * n + 256, 1);
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(77);
        let mut t = Sha256Transcript::new(b"rv");
        t.append_message(SIGHASH_LABEL, &sighash_of(env));
        let mut p = Prover::new(&pc, &mut t);
        p.set_backend(Backend::Bppp);
        let (cx, x) = p.commit(K::from(3u64), K::random(&mut rng));
        let (cy, y) = p.commit(K::from(5u64), K::random(&mut rng));
        circuit(&mut p, c, &[x, y], true);
        let proof = p.prove_with_rng(&bp, &mut rng).unwrap();
        let V = vec![cx, cy];
        let cc = match c { Circ::Product => Circ::Product, Circ::Chain(n) => Circ::Chain(*n), Circ::Table(a, b) => Circ::Table(*a, *b) };
        let mk = move || {
            let mut ct = CompileTranscript::new(b"rv");
            TranscriptBackend::append_message(&mut ct, SIGHASH_LABEL, &[0u8; 32]);
            let mut v = Verifier::<_, Secp256k1>::new(&mut ct);
            v.set_backend(Backend::Bppp);
            let (x, y) = (v.commit(V[0]), v.commit(V[1]));
            circuit(&mut v, &cc, &[x, y], false);
            v.compile_to_simplicity(&pc, &bp).unwrap()
        };
        (proof, Box::new(mk))
    }

    fn to_bytes(bits: &[bool]) -> Vec<u8> {
        bits.chunks(8).map(|c| c.iter().fold(0u8, |a, b| (a << 1) | *b as u8)).collect()
    }

    /// Bad witnesses: every point's parity flipped, every point's x + 1, every scalar + 1 and + n.
    fn bad_witnesses(w: &SimplicityWitness, sv: &SimplicityVerifier) -> Vec<(String, SimplicityWitness)> {
        let mut out = Vec::new();
        let st = sv.stats();
        let n_order = k256::U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
        for i in 0..st.witness_points {
            let name: Arc<str> = Arc::from(format!("p{}", i));
            let bits: Vec<bool> = w.0[&name].iter_padded().collect();
            assert_eq!(bits.len(), 257);
            let parity = bits[0];
            let xb = to_bytes(&bits[1..]);
            let mut b = w.clone();
            b.0.insert(name.clone(), ::simplicity::Value::product(bit_value(!parity), word_value(&xb)));
            out.push((format!("{} parity", name), b));
            let mut xb2 = xb.clone();
            xb2[31] ^= 1;
            let mut b = w.clone();
            b.0.insert(name.clone(), ::simplicity::Value::product(bit_value(parity), word_value(&xb2)));
            out.push((format!("{} x^1", name), b));
        }
        for i in 0..st.witness_scalars {
            let name: Arc<str> = Arc::from(format!("s{}", i));
            let sb = to_bytes(&w.0[&name].iter_padded().collect::<Vec<bool>>());
            let s = k256::U256::from_be_slice(&sb);
            let plus1 = s.wrapping_add(&k256::U256::ONE);
            let mut b = w.clone();
            b.0.insert(name.clone(), word_value(&k256::elliptic_curve::bigint::Encoding::to_be_bytes(&plus1)));
            out.push((format!("{} +1", name), b));
            let (plusn, carry) = s.adc(&n_order, k256::elliptic_curve::bigint::Limb::ZERO);
            if carry == k256::elliptic_curve::bigint::Limb::ZERO {
                let mut b = w.clone();
                b.0.insert(name.clone(), word_value(&k256::elliptic_curve::bigint::Encoding::to_be_bytes(&plusn)));
                out.push((format!("{} +n", name), b));
            }
        }
        out
    }

    /// A sample of 8 lowerings in which every option takes every value (both generator modes,
    /// 1 to 3 role passes, each switch on and off).
    fn sample_opts() -> Vec<(bool, Options)> {
        [(false, 1, false, false, false), (true, 1, false, true, false), (false, 2, true, false, true), (true, 2, true, true, true), (false, 3, false, true, true), (true, 3, true, false, false), (false, 1, true, true, true), (true, 2, false, false, true)]
            .iter()
            .map(|&(c, role_passes, hot_cold, small_words, shared_funcs)| (c, Options { role_passes, hot_cold, small_words, shared_funcs }))
            .collect()
    }

    /// Every lowering in `opts` on the verifiers of `circuits`: the honest proof passes, every
    /// bad witness (a point's parity or x, a scalar + 1 or + n) and another transaction fail.
    fn lowerings_reject_bad_witnesses(circuits: Vec<Circ>, opts: Vec<(bool, Options)>) {
        let env = dummy_env();
        for c in circuits {
            let (proof, mk) = compile_circ(&c, &env);
            FORCE.with(|f| *f.borrow_mut() = None);
            let sv0 = mk();
            let chosen = sv0.stats().lowering.clone();
            let w0 = sv0.witness(&proof).unwrap();
            let r0 = sv0.execute(&w0, &env);
            println!("default choice {}: {:?}", chosen, r0.as_ref().map(|r| (r.cost_mwu, r.budget_mwu)));
            let bads = bad_witnesses(&w0, &sv0);
            let mut cmrs = std::collections::HashSet::new();
            for &(compressed, o) in &opts {
                FORCE.with(|f| *f.borrow_mut() = Some((compressed, o)));
                let sv = mk();
                cmrs.insert(sv.cmr());
                let w = sv.witness(&proof).unwrap();
                let r = crate::simplicity::run::execute_term(&sv.term, &w.0, &env, false);
                assert!(r.is_ok(), "{:?} {:?}: honest rejected {:?}", compressed, o, r.err());
                for (what, b) in &bads {
                    let r = crate::simplicity::run::execute_term(&sv.term, &b.0, &env, false);
                    assert!(r.is_err(), "{:?} {:?}: accepted bad witness {}", compressed, o, what);
                }
                let r = crate::simplicity::run::execute_term(&sv.term, &w.0, &crate::simplicity::run::dummy_env_with_output(7), false);
                assert!(r.is_err(), "{:?} {:?}: accepted another tx", compressed, o);
            }
            FORCE.with(|f| *f.borrow_mut() = None);
            println!("{} distinct programs over {} lowerings, {} bad witnesses each", cmrs.len(), opts.len(), bads.len());
        }
    }

    /// A sample of lowerings on a product and a lookup table (products of many factors).
    #[test]
    fn sampled_lowerings_reject_bad_witnesses() {
        lowerings_reject_bad_witnesses(vec![Circ::Product, Circ::Table(16, 4)], sample_opts());
    }

    /// All 48 lowerings on a product, a chain and a lookup table (long: run in release with
    /// `--ignored`).
    #[test]
    #[ignore]
    fn every_lowering_rejects_bad_witnesses() {
        lowerings_reject_bad_witnesses(vec![Circ::Product, Circ::Chain(8), Circ::Table(16, 4)], all_opts());
    }

}

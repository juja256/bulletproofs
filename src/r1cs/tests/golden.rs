//! Golden proofs: with fixed randomness the prover must produce exactly the bytes that the
//! upstream code (zkcrypto/bulletproofs as of d27dde0) produces. Guards the memory and
//! parallelism optimisations of the prover and the inner-product argument, which must not
//! change any value of the protocol.
//!
//! `cargo test --release --lib r1cs::tests::golden` (also with `parallel`).


use crate::r1cs::*;
use crate::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};
use crate::curve::Ristretto;

/// A fixed "RNG" (64-bit LCG) — for test vectors only.
struct FixedRng(u64);

impl RngCore for FixedRng {
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        rand_core::impls::fill_bytes_via_next(self, dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}
impl CryptoRng for FixedRng {}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Shuffle gadget (as in tests/r1cs.rs): committed inputs, multipliers and randomized
/// (second-phase) constraints.
fn shuffle<CS: RandomizableConstraintSystem<Scalar>>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) -> Result<(), R1CSError> {
    let k = x.len();
    if k == 1 {
        cs.constrain(lc(y[0]) - x[0]);
        return Ok(());
    }
    cs.specify_randomized_constraints(move |cs| {
        let z = cs.challenge_scalar(b"shuffle challenge");
        let last_mulx_out = cs.multiply(x[k - 1] - z, x[k - 2] - z).2;
        let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
            let o = cs.multiply(prev_out.into(), x[i] - z).2;
            o
        });
        let last_muly_out = cs.multiply(y[k - 1] - z, y[k - 2] - z).2;
        let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
            let o = cs.multiply(prev_out.into(), y[i] - z).2;
            o
        });
        cs.constrain(lc(first_mulx_out) - first_muly_out);
        Ok(())
    })
}

/// A circuit with committed values, a first phase (multipliers, free witnesses, linear
/// constraints with repeated and non-unit coefficients) and a second phase. Upstream made the
/// squares with `allocate_multiplier` and the lone value with `allocate`: two witnesses folded
/// into a multiplier and a free witness (half a packed multiplier) are the same circuit.
fn circuit_proof(k: usize) -> (Vec<u8>, bool) {
    let pc_gens = PedersenGens::<Ristretto>::default();
    let bp_gens = BulletproofGens::new((2 * k + 8).next_power_of_two(), 1);
    let xs: Vec<u64> = (0..k as u64).map(|i| 3 * i + 1).collect();
    let ys: Vec<u64> = xs.iter().rev().copied().collect();

    let mut t = Transcript::new(b"golden");
    let mut prover = Prover::new(&pc_gens, &mut t);
    let (comms_x, vars_x): (Vec<_>, Vec<_>) =
        xs.iter().enumerate().map(|(i, v)| prover.commit(Scalar::from(*v), Scalar::from(1000 + i as u64))).unzip();
    let (comms_y, vars_y): (Vec<_>, Vec<_>) =
        ys.iter().enumerate().map(|(i, v)| prover.commit(Scalar::from(*v), Scalar::from(2000 + i as u64))).unzip();
    let extra = |cs: &mut dyn ConstraintSystem<Scalar>, vals: Option<&[u64]>| {
        // squares of the first few inputs, an unpaired allocation, a weighted sum
        for i in 0..3 {
            let a = vals.map(|v| Scalar::from(v[i]));
            let (l, r) = (cs.witness(a).unwrap(), cs.witness(a).unwrap());
            let o = cs.multiply(l.into(), r.into()).unwrap();
            cs.constrain(lc(l) - r);
            cs.constrain(o * Scalar::from(7u64) - l * Scalar::from(7 * 3 * i as u64 + 7) + Scalar::from(0u64));
        }
        let lone = cs.witness(vals.map(|_| Scalar::from(5u64))).unwrap();
        cs.constrain(lone - Scalar::from(5u64));
    };
    extra(&mut prover, Some(&xs));
    shuffle(&mut prover, vars_x, vars_y).unwrap();
    let proof = prover.prove_with_rng(&bp_gens, &mut FixedRng(1)).unwrap();

    let mut t = Transcript::new(b"golden");
    let mut verifier = Verifier::new(&mut t);
    let vx: Vec<_> = comms_x.iter().map(|c| verifier.commit(*c)).collect();
    let vy: Vec<_> = comms_y.iter().map(|c| verifier.commit(*c)).collect();
    extra(&mut verifier, None);
    shuffle(&mut verifier, vx, vy).unwrap();
    let ok = verifier.verify(&proof, &pc_gens, &bp_gens).is_ok();
    (proof.to_bytes(), ok)
}

/// A BP proof of a circuit with folded witnesses (this fork, not upstream): witnesses alone in
/// the inputs of `multiply` and `constrain_product`, read again elsewhere, next to free ones.
fn folded_circuit_proof() -> (Vec<u8>, bool) {
    let pc_gens = PedersenGens::<Ristretto>::default();
    let bp_gens = BulletproofGens::new(16, 1);
    let gadget = |cs: &mut dyn ConstraintSystem<Scalar>, prover: bool| {
        let v = |x: u64| prover.then(|| Scalar::from(x));
        let (a, b, c) = (cs.witness(v(3)).unwrap(), cs.witness(v(5)).unwrap(), cs.witness(v(7)).unwrap());
        let ab = cs.multiply(a.into(), b.into()).unwrap();
        cs.constrain_product(c.into(), lc(a) + 1u64, lc(ab) + 13u64).unwrap();
        let free = cs.witness(v(9)).unwrap();
        cs.constrain(lc(free) - a - ab * Scalar::from(2u64) + 24u64);
        cs.constrain(lc(c) - 7u64);
    };
    let mut t = Transcript::new(b"golden folded");
    let mut prover = Prover::new(&pc_gens, &mut t);
    gadget(&mut prover, true);
    let proof = prover.prove_with_rng(&bp_gens, &mut FixedRng(3)).unwrap();
    let mut t = Transcript::new(b"golden folded");
    let mut verifier = Verifier::new(&mut t);
    gadget(&mut verifier, false);
    let ok = verifier.verify(&proof, &pc_gens, &bp_gens).is_ok();
    (proof.to_bytes(), ok)
}

fn range_proof_bytes() -> Vec<u8> {
    let pc_gens = PedersenGens::<Ristretto>::default();
    let bp_gens = BulletproofGens::new(64, 8);
    let values = [3u64, 1 << 40, 77, u32::MAX as u64];
    let blindings: Vec<Scalar> = (0..4u64).map(|i| Scalar::from(31 + i)).collect();
    let mut t = Transcript::new(b"golden range");
    let (proof, _) =
        RangeProof::prove_multiple_with_rng(&bp_gens, &pc_gens, &mut t, &values, &blindings, 64, &mut FixedRng(2))
            .unwrap();
    proof.to_bytes()
}

// Generated by the upstream prover (d27dde0) with the same fixed randomness.
const CIRCUIT_7: &str = "01ee570991fd4aa9ca98a62288bfde99b8920c92217c31994cdd7beac08a44b14594d8ba24ae7d8b7424d555dff2922edd6596b95d9ba8100e5bf8b122045fb50ff032095c455878a058583fd82094ae6b6275b35e63e6a892f4fd9e2d09559c2cd4dfd4b44aff3449d575e297da331388b34c71e84cf9f289542f47fbf0f25a5cd46bad6fc0741f86b2c0b6c315eeb1a05cae454f6ed6c0579e287f4aea695d504af72a514fe0726fdd5ba341e73c3d9e4a55292924e40edb117aebfc0e6c8d17a805484f8d582cb53ccb81f87ffdd5b2053f410fc3bb2e66443e10937db50d2f8490a6bb70550d1c6c96407f4787343b7dd9ce83707c4cc0baa22ba1713bc87aac3fd9633574412d145b86a88b9c3ff2b7df1a14acd12e55ff74b1ff3966a11c64fb98cb30fb0446b5ac53dd6cd70aba9728e397df824f229da5785653ec85048cc8d8fa73e3991ef4c7458dcb56ba8c2d3dccd3a05d77c63cfc79d3d60c902e0cfecec79c0b20319d2aa01f34ad8f6b40e32c28758993721c4bde9221314d0329a00707375074c6866d0a5887d0aef210c43f75014599400bcc38b8f28b710489bb81bdacf3afacf7b2bc3d44d5e0bb10b6f97ad17d1b3359a896b86bb7a70bf8167b326ce1fcc50a34d6999242b61b7bc22db6a55f7c86b1d037635934bc10e656ce8bef5adf51b6d3a66de19a9aca38f671810f4d72a98967a51734bfe715544d60c80f7b1eede86b1e2cae248aca13c72a93b55f190f0d750a33b1604b1956467d629e61eb49fdddee4a66d27c3c2e04e5794986b51b244863e01d3b893cccd1deb0d50f70fb3a7af892c8253bdd2fd74e6a85fc1357ec9b8816edaa4d6d288b96e5547f9687d817576e779fad2e919a6c7fd18e05a7b3d706431972e200e24d27dc45de47d88919084a98910a117b88878ec577921911cfa458bac7646be8caef1703cc8253a031577e25765451ca3b3e48431d7c8e9a2eae0f370d6d6613a40b3831e7c6719a81aede90a8b9317832a6aed8278be92b02befdec87bd005a4096cdd9f3c3c3ab07925d28365b5508930bd47230852ea4029be9b7f1a706";
const CIRCUIT_40: &str = "01641a0012da995b02ba6c34e858979cf99812947c50627eb6b9d285fdf95b9f20ac45b5071929c5fcfbff962e7a4bb6c9986bb1ab162185b91201f6c0115dd55cc675cda2c6b3b70a346803c36d8401473f27a86d935c1b965579b3e95373873facccd5aff5805f90c59951e8b895d6193acbc32da33e0845c3859f7426efc0455097954cfecdb24e6b9da94c45819800458cb4c7dabd9d878366bd20277ef95db2e28278b98e9fb96b1c3fefb676ccf45905cd6163aaa2f1b1c9b48fcf9eb12a9ed4eb8ca8dd0ec1740c0f7240fab3787123fa663d97c6d988aeec49fda64f4c80dfcdb17c9d9417d97feffe4ea9c03acbb128f3ec42f52108ae0094b4fb177bce53b4b41c0f3ebb880919e43c134dacfaa6a4fbc9f4d132a9b199fd0c311377bc7957d50b154ee455740f6a0e0e7cf29bcf94dca9b5d4610680ffe687d55215bc373f1cdf0cf4edb57caf52b8b14ad837543d8aa8114af394c7bbe3e0e59a7adbc5d6d728e6329de1e91ef6ef7de06235d447aaff6bccf08a18b56263c474049d995cdbfe8d35c584233946bd518d23797f1ec7938f96220ed54960b9f516096135c1b005e0e7a64db87493fc7aa1c86f06d09588d58d4f98649b9633715c047a27f5a07ec8c237ee1b2e21ce898a366854164004fc171bb88604b3841dbd4a128785b77f7f4c518cafc3428b94e0bfd4c044b7162adfe87b82f43cdcef4f598a284171550a668c7ebbb73f6cd44504e0402a63b336ddffb4c0c174d31b8a5d56572b06e30ff247e5f3dc21b9943ed661d7758325d9b527cab56ade95035a0f364f87e5c55970032dbc689d55b66f7cfbebc5cc4eb62199828ed18d6f97351fb41ae98cc030b0c1afab0658242ebc86afcaafa04654940ea605b26abab4e41202bd45a84e99e7dac8a7b71c8f19b41fdc7a1dec44b47026873fb6a28bea6b3cac20d674a3c4da4475f3310e3f3891df0ba723948639b227a95c59408c593f1c0cea1a1e3056fad4b5843a70e182b3f32ff599f11f20bdbe5c89cf3641d066554c9376e87691f6aab7b80cb48dfdc6fb9ac61998c38a3f3e53756951443936648864ca2063bbd2a4cbdd8fe8d554fc1d1825c6895f3e50273a774f915a85740512fee42f5795be7d1ae1d77d0456e380caee20aa68d68211ae019fb0071a0a5dcead029f635dbf1aae9400da3d6878b41db5d1e881c09cb86675600400fc4e1658a9594f546b7e35c2b6c5beefebb1cae550335339030e014e3df516e1fcaa13c5a64dd61b7905daf57a24679e5d109048b7f54aedeeb683fc6cb4decd5e1006db7133bb25ffd0a8e937adb40acb44ab058b0078d058de59c8f7566468edac0c";
// k = 10000: about 20k multipliers padded to 2^15, so that every chunked loop of the
// prover (polynomial passes, constant-time and variable-time multiscalar multiplications,
// deferred inner-product rounds) runs over several chunks.
const CIRCUIT_10000: &str = "01e4e90f863a1ebf484cb2d728e5fe23bd1ca7f6ac9970681f0f82aaae091ab51474b8c578927e815aaa1e2ad298befda15633f58730d3418bafcaa23322fabc341289430366397a489cbe469a6ac0cf1204c0e7d7927c9041e8ac1508757b977da230988d924d0527482766aeba5129afe35ae5ec65cb08904f0b61062d158d5ae8faa72c3548d10052a678063058c988c0de193b6cd7b2bdb5f3d628507ca74e7a176d8158952e8e258e44e41fcaa0b24d42f408a5dba1f019fa4c484c77c5441ae257fad62ed6dd460b863b5e0b37a4e3fb258028ab795cac6090ebad282720944effbe9e360d6cd8682c33b3a2bc13330703d33cd49af8f86481a6adbb8667f61f07f5bab0833688f2b2093547308154e627b78a73950a9079df82b0bf01767246272c788170044b06f4b3aa8f3ff2663c40714580d3cd2a5168c801c317734e80475a5b619ebe479e62d901703c06cc093b70a5956192e11d5c427e5c4a007d0f760574730c5b1dab221b7a5a8342c9996fb47d158fef8b4c0a1e18ae18038bd1d7a2468c21992be769571159e8c032816e0aef01c72e05d63c1f45c38c021d41c88ef0e98216a50c8049c41090ecf14fe2599f93d2c94f9558d3ba71510cc4aeb7679a1808093c326fa70869455bddb47042b282a69e851d7ce408ae2f568c99b9db540d5ad92aed59a9caacf20fca79db60d728105427123a6450f8841dae7ef9180c151c18d2b75b6ec0799c03981c844a99ddd0eb3e379321fe8e1779ea1713fe64be5f222684a3229c6228a0e1cfe43a279a4bbe1b3444b8eedb18322a1006fb4b71f9c115df9cb993576fc9f9876e449aa43ba97a820b3aefb87129c84cfb14787a9e1fa6e277801ba3b8afa3b928182147171a17d53116b0720f64608d641470d5ddadf84e494f5c9de04f83a0baa70c9f8bba07900005caa3e103b26e1813ca253c74d238cd865a165e4a41bc28a0099db28742086af8211ac5126c9a8f3c5a9ddaf18a30c08ddb662ede24c863ac93b977490977fee28c98c94b0c2fdbdeb5f2dd6f354777b55fedb5e2791ead189051df70a703913787dadc627853e1ecddc21baf2f3f37cd9314f9bd63342391c34a70c9701e329695cbe70b461366c1b7692d02e4bdc84e83e9c3f5aaaad96da3b6d118252870bf2106f319ca3032b6b083415ffd3bc53cbf50f85ed4ba5ef950c3173d554f1494634c2c63f44e2bc5a2243ac0b48b171b4998644eaab26d8f68e63839af9e761b76f9e502ea0a6c45a3988b6cad0a30978f06cba7185f213720ea1334fd99031b2d30a24a70fd4bf87420cae8bfca5381d8daac3e3802cb5dac79a133058a79fa9173152d6c6dbea159865da44f4acc0738445965e8f0b353bf3be4676b75ba0f2e999464c61c2641ff4eb0e42178eee3dcf614d34e17bd90af2f379af8e198e5ee6d4d55d65062545f0e8541928161e595ba9a158fcf45137b4eccb9d0ac562c0b2b364bea9b2a4352b04ca67831fae8e8e30bea6ebe41320d0bd6bc49e3264800a8216df6561126200392a6bccccb69343bec0972ef92db74b5fd8a064c3c027b2011063c444dc1639ecfb4c1a68d7fca9e7a8e1c97e539ad270d76fac1255c1858db245e4d44142220684d913041308a30ed54d6dd47325148e6b85d4f3d0b705812775a09466abc78ab359f1a2b6345d1f11125c593b17dd43929b8d813612f3ce6280cbce4bd83df4c961d7c7b5d35d87078f00a2e02d50f1c32dc301a1f8f374f208ae6858a4c866e9cbfe8cf9b05bfdf326484a4658cb1daa7516ed84e8219fe7e4430347ad4f5a557e448471a9c440ef6de294ce6d93dc0f29fde0d291d1de13acef1cdb820c910e310352840d631d5bf7a6991b473d5725cb51e4fb787c1422a9c1b8cf351302be28788d19fe4a09dfe98f248a56915ce12f7ddd90175d2fd5d0eb44b55a43cf350bd1c9a2e0c0ccf949ebfa547eb71a0e09525dd879785385d6fc59c1c10733e63a870d46e61592a6333c32ba65a7dabd238fa03a072dad50c9a60dc52c0823624348889a45621b3e36d1b154b284b778eb74b2e30406cd80d";
const RANGE_4X64: &str = "aa4f00469d670c350cbeafec6790973b3da957b64f9f17af8e324f914798bc587ee1895350e0b021b3d3186d296b384c8c35187da4fffc5be1d2be9fef684d5ffa5981796166a23995028b0e65b381a11dbee1b96d7dd98606a9b06f248a9417767e916c782ca1e562271bfcb7bfaa784cef5c98a9fd5235e9cb5569b533e920ca7cd8c6ff81e3e231b01ebb112aad59f4ce201c11df3d96b356d30d9700740a90132f146ff4af3761062136ff4ad12b82d77fba3ceaacdae43b6f1ab883700c38d2ca82def0f9301f71bf52336d074e5820f4875bbf6708034af089409b410b4a0a7a0debd7b13b206c9a17aa8a67f3a02033caac4345736624e73ee9272a6a16c52254427cc0cbb4fdd5f58adfdc487cb05a4a470d97640ec4a9207523ce450e1b48d7bdfc4a25c8306e98a744dba10f72c22acbe18e077d25dd6586fbc73b48359bfd0c9b35d9751bd6b4093d4f29cb5d7d89bc29d38924966afbd47afc210c3e3eae110ad882689da674a500c8d302ba420a04e0a732404ef6245a084a575276a0c5a99ccbeaaf942c31d20edede08a66f7db03e342243b71d04171b5f193a51473556c9ea6b7b7ce5359f23a8fe2fb19edc998646d424391d729620717c14dd4fde866ca5c3ce92ebd0897ee8d51777d31ae40513e2e41f44562211332f5246c40f7e7ca6b33d50757ebd46cf7d3049995096c617a5baea652be9c8e44de258087846a9abc7a49c566a98af4cdf306a56eaed863ee6a4bee05ea2f20e474a3540dbab2b7706075dbd8f7102760ede0acb1f5dae6066fec040c4ba9d4c21329f4d1f68c01d6ce48ed22a92d8c6296c78e6b1caac0ad4deb4891b2fe4333336268385ec7e04025338bdc4745dfea0e8437f09f06b5060b5e4b1ae29d27026b6568cf92d8fb9c67695421c0f4a1fefd3217696425ab7a91fab1db9f44c1e36722bcaea5874b927613a835e29e6554c4ad07922b7b982c78b1834e428c5c02962776b3dfa803b18e8fe2e3f8afc234a159c0f143b5b7adac29220c03b01d6111a5bfd9551c91e59cb93ed8ece02d015a1f0cfc2dc1a41f58659ba0ea69b800d89fc747d751149e29e026791d4045808a6b2670ef655843effa2c18eeac6940e";

#[test]
fn golden_circuit_proofs() {
    for (k, expected) in [(7, CIRCUIT_7), (40, CIRCUIT_40)] {
        let (bytes, ok) = circuit_proof(k);
        assert!(ok, "k = {}: proof does not verify", k);
        println!("CIRCUIT_{k} {}", hex(&bytes));
        assert_eq!(hex(&bytes), expected, "k = {k}: proof bytes changed");
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "slow without optimisations; run with --release")]
fn golden_circuit_proof_large() {
    let (bytes, ok) = circuit_proof(10000);
    assert!(ok, "proof does not verify");
    println!("CIRCUIT_10000 {}", hex(&bytes));
    assert_eq!(hex(&bytes), CIRCUIT_10000, "proof bytes changed");
}

// Generated by this code (2026-10-22): pins the BP encoding of folded witnesses.
const FOLDED: &str = "00ead0f22d20b989dbfc07a3bdbdbe01ff22bdb9359f9d2ac3efd10b1320b4730efe74f28dd52d1dc10e82b000fae2e7ab2b2dc2edbe3796b284b10a7aca05463fb49e7b92a5db529e1b6914b23a79ae2e9c02b5a63244476e1fe1b0411abe03468a574605854ecc84ae16456e182587f5b2ff70864742e0ef81cc5ea701d9d244d4d02ad3b142167e7462847cc277237dd4426bd49fcece327e3e0869cf832b3d48482ab0ddd085625dc01199e7a93dd19b83fbd61710e016e231386cdee12840ba35ecb89004b25914321794247029acdf1cc9de4009225c82caae224bcf543710fbef8d9013d994910511a8370e5a4095c4732f80770c7f232a38e23eebd2615ac56bef0d3b96985e03cc35411057ae04d5de4d91a14f4130687242a3e7ad0fa959daf7c6d45eb53590e07db15b205d499c1f7c3d1f2f3dc54f9cb156c1eb0dba36aff1a12c98ec35f3ced6ff2f52589c772ac0377cd394bbae1e4396a6b4067a96d11349f48fa61da01b17fd1f5b2f01e385bd59658ff2e40d2a6cc02a4c566494ca157744b899ac442b6f73905a59a0df5d9134020429370f3600e28327448028734805809e50f27793d58cca2ce71d1274142c3be1d602f827b74c7ec953026473fe51b573f988219f393c5ea350f4964a50f9604df18237a5af9b87a83939d0a84a20f550fe3df115d7f5fa24346a238bec74f600a870875856fe54550a3b520b400c0e2710ffad2e4ace8f9e6e7aa7b379c32dab6119047e5f93333901";

#[test]
fn golden_folded_circuit_proof() {
    let (bytes, ok) = folded_circuit_proof();
    assert!(ok, "proof does not verify");
    println!("FOLDED {}", hex(&bytes));
    assert_eq!(hex(&bytes), FOLDED, "proof bytes changed");
}

#[test]
fn golden_range_proof() {
    let bytes = range_proof_bytes();
    println!("RANGE_4X64 {}", hex(&bytes));
    assert_eq!(hex(&bytes), RANGE_4X64, "range proof bytes changed");
}

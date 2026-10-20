//! ristretto255 (curve25519-dalek): the default curve, byte-identical to the upstream crate.

use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_COMPRESSED, RISTRETTO_BASEPOINT_POINT};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use sha3::Sha3_512;

use super::Curve;
use crate::util;

/// ristretto255 (curve25519-dalek).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Ristretto;

impl Curve for Ristretto {
    type Scalar = Scalar;
    type Point = RistrettoPoint;
    type Compressed = CompressedRistretto;
    const NAME: &'static str = "ristretto255";
    const POINT_BYTES: usize = 32;

    fn compress(p: &RistrettoPoint) -> CompressedRistretto {
        p.compress()
    }

    fn compressed_bytes(c: &CompressedRistretto) -> &[u8] {
        c.as_bytes()
    }

    fn decompress(c: &CompressedRistretto) -> Option<RistrettoPoint> {
        c.decompress()
    }

    fn compressed_from_slice(bytes: &[u8]) -> Option<CompressedRistretto> {
        CompressedRistretto::from_slice(bytes).ok()
    }

    fn scalar_from_wide(bytes: &[u8; 64]) -> Scalar {
        Scalar::from_bytes_mod_order_wide(bytes)
    }

    fn scalar_to_bytes(s: &Scalar) -> [u8; 32] {
        s.to_bytes()
    }

    fn scalar_from_canonical(bytes: &[u8; 32]) -> Option<Scalar> {
        Option::from(Scalar::from_canonical_bytes(*bytes))
    }

    fn point_from_uniform(bytes: &[u8; 64]) -> RistrettoPoint {
        RistrettoPoint::from_uniform_bytes(bytes)
    }

    fn default_pedersen() -> (RistrettoPoint, RistrettoPoint) {
        let blinding = RistrettoPoint::hash_from_bytes::<Sha3_512>(RISTRETTO_BASEPOINT_COMPRESSED.as_bytes());
        (RISTRETTO_BASEPOINT_POINT, blinding)
    }

    fn msm_ct(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
        util::msm_slices(s, p, util::MSM_CHUNK_CT, false)
    }

    fn msm_vt(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
        util::msm_slices(s, p, util::MSM_CHUNK_VT, true)
    }

    fn batch_invert(s: &mut [Scalar]) -> Scalar {
        Scalar::batch_invert(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::ristretto::RistrettoPoint;
    use curve25519_dalek::scalar::Scalar;
    use curve25519_dalek::traits::MultiscalarMul;
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn ristretto_matches_dalek() {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let s: Vec<Scalar> = (0..100).map(|_| Scalar::random(&mut rng)).collect();
        let p: Vec<RistrettoPoint> = (0..100).map(|_| RistrettoPoint::random(&mut rng)).collect();
        let direct = RistrettoPoint::multiscalar_mul(&s, &p);
        assert_eq!(Ristretto::msm_ct(&s, &p), direct);
        assert_eq!(Ristretto::msm_vt(&s, &p), direct);
        let c = Ristretto::compress(&p[0]);
        assert_eq!(Ristretto::compressed_bytes(&c), p[0].compress().as_bytes());
        assert_eq!(Ristretto::decompress(&c), Some(p[0]));
        assert_eq!(Ristretto::compressed_from_slice(&[0u8; 31]), None);
        let wide = [7u8; 64];
        assert_eq!(Ristretto::scalar_from_wide(&wide), Scalar::from_bytes_mod_order_wide(&wide));
        assert_eq!(Ristretto::scalar_to_bytes(&s[0]), s[0].to_bytes());
        assert_eq!(Ristretto::scalar_from_canonical(&s[0].to_bytes()), Some(s[0]));
        assert_eq!(Ristretto::scalar_from_canonical(&[0xff; 32]), None);
        assert_eq!(Ristretto::point_from_uniform(&wide), RistrettoPoint::from_uniform_bytes(&wide));
        let (b, bb) = Ristretto::default_pedersen();
        let pg = crate::PedersenGens::default();
        assert_eq!((b, bb), (pg.B, pg.B_blinding));
        let mut inv = s[..5].to_vec();
        let all = Ristretto::batch_invert(&mut inv);
        assert!(inv.iter().zip(&s).all(|(i, x)| i * x == Scalar::ONE));
        assert_eq!(all, s[..5].iter().product::<Scalar>().invert());
        assert_eq!(Ristretto::POINT_BYTES, 32);
        assert_eq!(Ristretto::NAME, "ristretto255");
    }
}

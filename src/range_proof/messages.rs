//! The `messages` module contains the API for the messages passed between the parties and the dealer
//! in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

extern crate alloc;

use alloc::vec::Vec;
use core::iter;

use crate::curve::{Curve, Ristretto};
use crate::generators::{BulletproofGens, PedersenGens};

/// A commitment to the bits of a party's value. The points are encoded (for ristretto255 the
/// serialization is that of the upstream crate, which serializes points compressed).
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
#[serde(bound = "")]
pub struct BitCommitment<C: Curve = Ristretto> {
    pub(super) V_j: C::Compressed,
    pub(super) A_j: C::Compressed,
    pub(super) S_j: C::Compressed,
}

/// Challenge values derived from all parties' [`BitCommitment`]s.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
#[serde(bound = "")]
pub struct BitChallenge<C: Curve = Ristretto> {
    pub(super) y: C::Scalar,
    pub(super) z: C::Scalar,
}

/// A commitment to a party's polynomial coefficents.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
#[serde(bound = "")]
pub struct PolyCommitment<C: Curve = Ristretto> {
    pub(super) T_1_j: C::Compressed,
    pub(super) T_2_j: C::Compressed,
}

/// Challenge values derived from all parties' [`PolyCommitment`]s.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
#[serde(bound = "")]
pub struct PolyChallenge<C: Curve = Ristretto> {
    pub(super) x: C::Scalar,
}

/// A party's proof share, ready for aggregation into the final
/// [`RangeProof`](::RangeProof).
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(bound = "")]
pub struct ProofShare<C: Curve = Ristretto> {
    pub(super) t_x: C::Scalar,
    pub(super) t_x_blinding: C::Scalar,
    pub(super) e_blinding: C::Scalar,
    pub(super) l_vec: Vec<C::Scalar>,
    pub(super) r_vec: Vec<C::Scalar>,
}

impl<C: Curve> ProofShare<C> {
    /// Checks consistency of all sizes in the proof share and returns the size of the l/r vector.
    pub(super) fn check_size(
        &self,
        expected_n: usize,
        bp_gens: &BulletproofGens<C>,
        j: usize,
    ) -> Result<(), ()> {
        if self.l_vec.len() != expected_n {
            return Err(());
        }

        if self.r_vec.len() != expected_n {
            return Err(());
        }

        if expected_n > bp_gens.gens_capacity {
            return Err(());
        }

        if j >= bp_gens.party_capacity {
            return Err(());
        }

        Ok(())
    }

    /// Audit an individual proof share to determine whether it is
    /// malformed.
    pub(super) fn audit_share(
        &self,
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        j: usize,
        bit_commitment: &BitCommitment<C>,
        bit_challenge: &BitChallenge<C>,
        poly_commitment: &PolyCommitment<C>,
        poly_challenge: &PolyChallenge<C>,
    ) -> Result<(), ()> {
        use crate::inner_product_proof::inner_product;
        use crate::util;
        use core::ops::Not;
        use ff::Field as _;
        use group::Group;

        let n = self.l_vec.len();

        self.check_size(n, bp_gens, j)?;

        let (y, z) = (bit_challenge.y, bit_challenge.z);
        let x = poly_challenge.x;

        // Precompute some variables
        let zz = z * z;
        let minus_z = -z;
        let z_j = util::scalar_exp_vartime(&z, j as u64); // z^j
        let y_jn = util::scalar_exp_vartime(&y, (j * n) as u64); // y^(j*n)
        let y_jn_inv = Option::<C::Scalar>::from(y_jn.invert()).ok_or(())?; // y^(-j*n)
        let y_inv = Option::<C::Scalar>::from(y.invert()).ok_or(())?; // y^(-1)

        if self.t_x != inner_product(&self.l_vec, &self.r_vec) {
            return Err(());
        }

        let g = self.l_vec.iter().map(|l_i| minus_z - l_i);
        let h = self
            .r_vec
            .iter()
            .zip(util::exp_iter(C::Scalar::from(2u64)))
            .zip(util::exp_iter(y_inv))
            .map(|((r_i, exp_2), exp_y_inv)| {
                z + exp_y_inv * y_jn_inv * (-*r_i) + exp_y_inv * y_jn_inv * (zz * z_j * exp_2)
            });

        let A_j = C::decompress(&bit_commitment.A_j).ok_or(())?;
        let S_j = C::decompress(&bit_commitment.S_j).ok_or(())?;
        let scalars: Vec<C::Scalar> = iter::once(C::Scalar::ONE)
            .chain(iter::once(x))
            .chain(iter::once(-self.e_blinding))
            .chain(g)
            .chain(h)
            .collect();
        let points: Vec<C::Point> = iter::once(A_j)
            .chain(iter::once(S_j))
            .chain(iter::once(pc_gens.B_blinding))
            .chain(bp_gens.share(j).G(n).copied())
            .chain(bp_gens.share(j).H(n).copied())
            .collect();
        let P_check = C::msm_vt(&scalars, &points);
        if P_check.is_identity().not().into() {
            return Err(());
        }

        let V_j = C::decompress(&bit_commitment.V_j).ok_or(())?;
        let T_1_j = C::decompress(&poly_commitment.T_1_j).ok_or(())?;
        let T_2_j = C::decompress(&poly_commitment.T_2_j).ok_or(())?;

        let sum_of_powers_y = util::sum_of_powers(&y, n);
        let sum_of_powers_2 = util::sum_of_powers(&C::Scalar::from(2u64), n);
        let delta = (z - zz) * sum_of_powers_y * y_jn - z * zz * sum_of_powers_2 * z_j;
        let t_check = C::msm_vt(
            &[zz * z_j, x, x * x, delta - self.t_x, -self.t_x_blinding],
            &[V_j, T_1_j, T_2_j, pc_gens.B, pc_gens.B_blinding],
        );

        if t_check.is_identity().into() {
            Ok(())
        } else {
            Err(())
        }
    }
}

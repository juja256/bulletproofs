//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use core::marker::PhantomData;
use digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake256, Shake256Reader};

use crate::curve::{Curve, Ristretto};

/// Represents a pair of base points for Pedersen commitments.
///
/// The Bulletproofs implementation and API is designed to support
/// pluggable bases for Pedersen commitments, so that the choice of
/// bases is not hard-coded.
///
/// The default generators are those of the curve (`Curve::default_pedersen`); for
/// ristretto255:
///
/// * `B`: the `ristretto255` basepoint;
/// * `B_blinding`: the result of `ristretto255` SHA3-512
/// hash-to-group on input `B_bytes`.
#[derive(Copy, Clone)]
pub struct PedersenGens<C: Curve = Ristretto> {
    /// Base for the committed value
    pub B: C::Point,
    /// Base for the blinding factor
    pub B_blinding: C::Point,
}

impl<C: Curve> PedersenGens<C> {
    /// The standard generators of the curve `C` (`Curve::default_pedersen`).
    pub fn for_curve() -> Self {
        let (B, B_blinding) = C::default_pedersen();
        PedersenGens { B, B_blinding }
    }

    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: C::Scalar, blinding: C::Scalar) -> C::Point {
        C::msm_ct(&[value, blinding], &[self.B, self.B_blinding])
    }
}

/// The ristretto255 generators. `Default` is implemented for the default curve only, so that
/// `PedersenGens::default()` keeps inferring ristretto255 (default type parameters do not take
/// part in inference); other curves use [`PedersenGens::for_curve`].
impl Default for PedersenGens<Ristretto> {
    fn default() -> Self {
        Self::for_curve()
    }
}

/// The `GeneratorsChain` creates an arbitrary-long sequence of
/// orthogonal generators.  The sequence can be deterministically
/// produced starting with an arbitrary point.
struct GeneratorsChain<C: Curve> {
    reader: Shake256Reader,
    _curve: PhantomData<C>,
}

impl<C: Curve> GeneratorsChain<C> {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut shake = Shake256::default();
        shake.update(b"GeneratorsChain");
        shake.update(label);

        GeneratorsChain {
            reader: shake.finalize_xof(),
            _curve: PhantomData,
        }
    }

    /// Advances the reader n times, squeezing and discarding
    /// the result.
    fn fast_forward(mut self, n: usize) -> Self {
        for _ in 0..n {
            let mut buf = [0u8; 64];
            self.reader.read(&mut buf);
        }
        self
    }
}

impl<C: Curve> GeneratorsChain<C> {
    /// Append the next `n` generators to `v`. The XOF is read sequentially; with the
    /// `parallel` feature the hash-to-group maps run on all threads.
    fn extend_vec(self, v: &mut Vec<C::Point>, n: usize) {
        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            let mut chain = self;
            const BATCH: usize = 1 << 14;
            let mut left = n;
            while left > 0 {
                let k = left.min(BATCH);
                let bytes: Vec<[u8; 64]> = (0..k)
                    .map(|_| {
                        let mut b = [0u8; 64];
                        chain.reader.read(&mut b);
                        b
                    })
                    .collect();
                let mut points = Vec::with_capacity(k);
                bytes.par_iter().map(|b| C::point_from_uniform(b)).collect_into_vec(&mut points);
                v.extend(points);
                left -= k;
            }
        }
        #[cfg(not(feature = "parallel"))]
        v.extend(self.take(n));
    }
}

impl<C: Curve> Default for GeneratorsChain<C> {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl<C: Curve> Iterator for GeneratorsChain<C> {
    type Item = C::Point;

    fn next(&mut self) -> Option<Self::Item> {
        let mut uniform_bytes = [0u8; 64];
        self.reader.read(&mut uniform_bytes);

        Some(C::point_from_uniform(&uniform_bytes))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// The `BulletproofGens` struct contains all the generators needed
/// for aggregating up to `m` range proofs of up to `n` bits each.
///
/// # Extensible Generator Generation
///
/// Instead of constructing a single vector of size `m*n`, as
/// described in the Bulletproofs paper, we construct each party's
/// generators separately.
///
/// To construct an arbitrary-length chain of generators, we apply
/// SHAKE256 to a domain separator label, and feed each 64 bytes of
/// XOF output into the `ristretto255` hash-to-group function.
/// Each of the `m` parties' generators are constructed using a
/// different domain separation label, and proving and verification
/// uses the first `n` elements of the arbitrary-length chain.
///
/// This means that the aggregation size (number of
/// parties) is orthogonal to the rangeproof size (number of bits),
/// and allows using the same `BulletproofGens` object for different
/// proving parameters.
///
/// This construction is also forward-compatible with constraint
/// system proofs, which use a much larger slice of the generator
/// chain, and even forward-compatible to multiparty aggregation of
/// constraint system proofs, since the generators are namespaced by
/// their party index.
#[derive(Clone)]
pub struct BulletproofGens<C: Curve = Ristretto> {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators for each party.
    G_vec: Vec<Vec<C::Point>>,
    /// Precomputed \\(\mathbf H\\) generators for each party.
    H_vec: Vec<Vec<C::Point>>,
}

impl BulletproofGens<Ristretto> {
    /// Create a new `BulletproofGens` object over ristretto255 (other curves:
    /// [`BulletproofGens::for_curve`]; `new` is defined for the default curve only so that
    /// `BulletproofGens::new(..)` keeps inferring it).
    pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        Self::for_curve(gens_capacity, party_capacity)
    }
}

impl<C: Curve> BulletproofGens<C> {
    /// Create a new `BulletproofGens` object over the curve `C`.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.  For rangeproofs, it is sufficient to pass
    ///    `64`, the maximum bitsize of the rangeproofs.  For circuit
    ///    proofs, the capacity must be greater than the number of
    ///    multipliers, rounded up to the next power of two.
    ///
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn for_curve(gens_capacity: usize, party_capacity: usize) -> Self {
        let mut gens = BulletproofGens {
            gens_capacity: 0,
            party_capacity,
            G_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
            H_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
        };
        gens.increase_capacity(gens_capacity);
        gens
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> BulletproofGensShare<'_, C> {
        BulletproofGensShare {
            gens: &self,
            share: j,
        }
    }

    /// Increases the generators' capacity to the amount specified.
    /// If less than or equal to the current capacity, does nothing.
    pub fn increase_capacity(&mut self, new_capacity: usize) {
        use byteorder::{ByteOrder, LittleEndian};

        if self.gens_capacity >= new_capacity {
            return;
        }

        let extra = new_capacity - self.gens_capacity;
        for i in 0..self.party_capacity {
            let party_index = i as u32;
            let mut label = [b'G', 0, 0, 0, 0];
            LittleEndian::write_u32(&mut label[1..5], party_index);
            let chain = GeneratorsChain::<C>::new(&label).fast_forward(self.gens_capacity);
            chain.extend_vec(&mut self.G_vec[i], extra);

            label[0] = b'H';
            let chain = GeneratorsChain::<C>::new(&label).fast_forward(self.gens_capacity);
            chain.extend_vec(&mut self.H_vec[i], extra);
        }
        self.gens_capacity = new_capacity;
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    pub(crate) fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &C::Point> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    pub(crate) fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &C::Point> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a, P> {
    array: &'a Vec<Vec<P>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a, P> Iterator for AggregatedGensIter<'a, P> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }

        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx][cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n * (self.m - self.party_idx) - self.gen_idx;
        (size, Some(size))
    }
}

/// Represents a view of the generators used by a specific party in an
/// aggregated proof.
///
/// The `BulletproofGens` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `BulletproofGensShare`
/// provides a view of the generators for one of the `m` parties' shares.
///
/// The `BulletproofGensShare` is produced by [`BulletproofGens::share()`].
pub struct BulletproofGensShare<'a, C: Curve = Ristretto> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens<C>,
    /// Which share we are
    share: usize,
}

// derived Copy/Clone would require C: Copy on the share's fields only through references
impl<'a, C: Curve> Clone for BulletproofGensShare<'a, C> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<'a, C: Curve> Copy for BulletproofGensShare<'a, C> {}

impl<'a, C: Curve> BulletproofGensShare<'a, C> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub fn G(&self, n: usize) -> impl Iterator<Item = &'a C::Point> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &'a C::Point> {
        self.gens.H_vec[self.share].iter().take(n)
    }

    /// The first `n` G and H generators of this party as slices.
    pub(crate) fn G_H_slices(&self, n: usize) -> (&'a [C::Point], &'a [C::Point]) {
        (&self.gens.G_vec[self.share][..n], &self.gens.H_vec[self.share][..n])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::ristretto::RistrettoPoint;

    #[test]
    fn aggregated_gens_iter_matches_flat_map() {
        let gens = BulletproofGens::new(64, 8);

        let helper = |n: usize, m: usize| {
            let agg_G: Vec<RistrettoPoint> = gens.G(n, m).cloned().collect();
            let flat_G: Vec<RistrettoPoint> = gens
                .G_vec
                .iter()
                .take(m)
                .flat_map(move |G_j| G_j.iter().take(n))
                .cloned()
                .collect();

            let agg_H: Vec<RistrettoPoint> = gens.H(n, m).cloned().collect();
            let flat_H: Vec<RistrettoPoint> = gens
                .H_vec
                .iter()
                .take(m)
                .flat_map(move |H_j| H_j.iter().take(n))
                .cloned()
                .collect();

            assert_eq!(agg_G, flat_G);
            assert_eq!(agg_H, flat_H);
        };

        helper(64, 8);
        helper(64, 4);
        helper(64, 2);
        helper(64, 1);
        helper(32, 8);
        helper(32, 4);
        helper(32, 2);
        helper(32, 1);
        helper(16, 8);
        helper(16, 4);
        helper(16, 2);
        helper(16, 1);
    }

    #[test]
    fn resizing_small_gens_matches_creating_bigger_gens() {
        let gens = BulletproofGens::new(64, 8);

        let mut gen_resized = BulletproofGens::new(32, 8);
        gen_resized.increase_capacity(64);

        let helper = |n: usize, m: usize| {
            let gens_G: Vec<RistrettoPoint> = gens.G(n, m).cloned().collect();
            let gens_H: Vec<RistrettoPoint> = gens.H(n, m).cloned().collect();

            let resized_G: Vec<RistrettoPoint> = gen_resized.G(n, m).cloned().collect();
            let resized_H: Vec<RistrettoPoint> = gen_resized.H(n, m).cloned().collect();

            assert_eq!(gens_G, resized_G);
            assert_eq!(gens_H, resized_H);
        };

        helper(64, 8);
        helper(32, 8);
        helper(16, 8);
    }
}

//! Constant-time multiplicity counting (spec §7.4) by an oblivious (bitonic) sort:
//! `O((|T| + |Q|) log^2)` comparisons whose sequence depends only on the sizes, instead of
//! `|T| |Q|`. The counts are those of the direct method: each lookup counts for the first row
//! equal to it.

use alloc::vec::Vec;

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater};


/// An element of the sort: a key (the row or the evaluated lookup, its components' bytes as
/// 64-bit limbs; any total order groups equal keys), whether it is a row, its index, and a
/// counter.
#[derive(Clone)]
struct Item {
    key: Vec<u64>,
    /// 0 row, 1 lookup, 2 padding (sorts last).
    kind: u8,
    index: u64,
    count: u64,
}

/// Swap `a` and `b` if `c` (constant time, in place).
fn swap_items(a: &mut Item, b: &mut Item, c: Choice) {
    for (x, y) in a.key.iter_mut().zip(b.key.iter_mut()) {
        u64::conditional_swap(x, y, c);
    }
    u8::conditional_swap(&mut a.kind, &mut b.kind, c);
    u64::conditional_swap(&mut a.index, &mut b.index, c);
    u64::conditional_swap(&mut a.count, &mut b.count, c);
}

/// `a > b` for limb strings of equal length, lexicographically (constant time).
fn gt_limbs(a: &[u64], b: &[u64]) -> Choice {
    let mut gt = Choice::from(0u8);
    let mut eq = Choice::from(1u8);
    for (x, y) in a.iter().zip(b) {
        gt |= eq & x.ct_gt(y);
        eq &= x.ct_eq(y);
    }
    gt
}

/// The sort order: key, then kind (rows before lookups), then index.
fn gt_items(a: &Item, b: &Item, by_key: bool) -> Choice {
    let kind_gt = a.kind.ct_gt(&b.kind);
    let kind_eq = a.kind.ct_eq(&b.kind);
    let idx_gt = a.index.ct_gt(&b.index);
    if by_key {
        let key_gt = gt_limbs(&a.key, &b.key);
        let key_eq = a.key.ct_eq(&b.key);
        key_gt | (key_eq & (kind_gt | (kind_eq & idx_gt)))
    } else {
        // Back to the input order: kind, then index.
        kind_gt | (kind_eq & idx_gt)
    }
}

/// Bitonic sort of a power-of-two number of items (data-independent sequence of
/// compare-exchanges).
fn bitonic_sort(v: &mut [Item], by_key: bool) {
    let n = v.len();
    debug_assert!(n.is_power_of_two());
    let mut k = 2;
    while k <= n {
        let mut j = k / 2;
        while j > 0 {
            for i in 0..n {
                let l = i ^ j;
                if l > i {
                    let ascending = i & k == 0;
                    let (lo, hi) = v.split_at_mut(l);
                    let (a, b) = (&mut lo[i], &mut hi[0]);
                    let gt = gt_items(a, b, by_key);
                    swap_items(a, b, if ascending { gt } else { !gt });
                }
            }
            j /= 2;
        }
        k *= 2;
    }
}

/// Multiplicities of `rows` among `lookups` (all keys of one length), each lookup counting
/// for the first equal row, and whether every lookup equals some row. Constant time in the
/// keys.
pub(super) fn count(rows: &[Vec<u8>], lookups: &[Vec<u8>]) -> (Vec<u64>, Choice) {
    let limbs = |b: &[u8]| -> Vec<u64> {
        b.chunks(8)
            .map(|c| {
                let mut x = [0u8; 8];
                x[..c.len()].copy_from_slice(c);
                u64::from_le_bytes(x)
            })
            .collect()
    };
    debug_assert!(rows.iter().chain(lookups).all(|k| k.len() == rows.first().map_or(k.len(), |r| r.len())), "keys of one length");
    let width = rows.first().map_or(0, |r| (r.len() + 7) / 8);
    let total = rows.len() + lookups.len();
    let n = total.next_power_of_two().max(1);
    let mut v: Vec<Item> = Vec::with_capacity(n);
    for (i, r) in rows.iter().enumerate() {
        v.push(Item { key: limbs(r), kind: 0, index: i as u64, count: 0 });
    }
    for (i, q) in lookups.iter().enumerate() {
        v.push(Item { key: limbs(q), kind: 1, index: i as u64, count: 0 });
    }
    while v.len() < n {
        v.push(Item { key: alloc::vec![u64::MAX; width], kind: 2, index: v.len() as u64, count: 0 });
    }
    bitonic_sort(&mut v, true);
    // Forward: every lookup must follow (in the run of its key) a row.
    let mut all_found = Choice::from(1u8);
    let mut have_row = Choice::from(0u8);
    for p in 0..n {
        let same = if p == 0 { Choice::from(0u8) } else { v[p].key.ct_eq(&v[p - 1].key) };
        let is_row = v[p].kind.ct_eq(&0);
        let is_lookup = v[p].kind.ct_eq(&1);
        have_row = is_row | (same & have_row);
        all_found &= !is_lookup | have_row;
    }
    // Backward: count the lookups of a key and give the count to its first row (rows of a key
    // come first, by index).
    let mut c = 0u64;
    for p in (0..n).rev() {
        let next_same = if p + 1 == n { Choice::from(0u8) } else { v[p].key.ct_eq(&v[p + 1].key) };
        c.conditional_assign(&0, !next_same);
        let is_lookup = v[p].kind.ct_eq(&1);
        let is_row = v[p].kind.ct_eq(&0);
        c += is_lookup.unwrap_u8() as u64;
        let first = if p == 0 { Choice::from(1u8) } else { !v[p].key.ct_eq(&v[p - 1].key) | !v[p - 1].kind.ct_eq(&0) };
        let first_row = is_row & first;
        v[p].count = u64::conditional_select(&0, &c, first_row);
    }
    bitonic_sort(&mut v, false);
    let out = v[..rows.len()].iter().map(|x| x.count).collect();
    v.iter_mut().for_each(|x| x.key.iter_mut().for_each(|l| *l = 0));
    (out, all_found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    fn naive(rows: &[Vec<u8>], lookups: &[Vec<u8>]) -> (Vec<u64>, bool) {
        let mut m = alloc::vec![0u64; rows.len()];
        let mut ok = true;
        for q in lookups {
            match rows.iter().position(|r| r == q) {
                Some(i) => m[i] += 1,
                None => ok = false,
            }
        }
        (m, ok)
    }

    #[test]
    fn matches_direct_counting() {
        let mut rng = rand::thread_rng();
        for _ in 0..300 {
            let width = rng.gen_range(1..4);
            let alphabet = rng.gen_range(1..6u8);
            let nr = rng.gen_range(1..12);
            let nq = rng.gen_range(0..20);
            let key = |rng: &mut rand::rngs::ThreadRng| (0..width).map(|_| rng.gen_range(0..alphabet)).collect::<Vec<u8>>();
            let rows: Vec<Vec<u8>> = (0..nr).map(|_| key(&mut rng)).collect();
            let lookups: Vec<Vec<u8>> = (0..nq)
                .map(|_| if rng.gen_bool(0.8) { rows[rng.gen_range(0..nr)].clone() } else { key(&mut rng) })
                .collect();
            let (m, ok) = count(&rows, &lookups);
            let (m2, ok2) = naive(&rows, &lookups);
            assert_eq!(m, m2, "rows {:?} lookups {:?}", rows, lookups);
            assert_eq!(bool::from(ok), ok2);
        }
    }

    #[test]
    fn keys_of_all_ones_and_padding() {
        // a key of 0xff bytes sorts with the padding: rows still come first
        let rows = alloc::vec![alloc::vec![0xffu8; 2], alloc::vec![0u8; 2]];
        let lookups = alloc::vec![alloc::vec![0xffu8; 2], alloc::vec![0xffu8; 2], alloc::vec![0u8; 2]];
        let (m, ok) = count(&rows, &lookups);
        assert_eq!(m, alloc::vec![2, 1]);
        assert!(bool::from(ok));
        let (m, ok) = count(&rows[1..], &lookups);
        assert_eq!(m, alloc::vec![1]);
        assert!(!bool::from(ok));
    }
}

#[cfg(test)]
mod timing {
    /// `cargo test --release --lib oblivious::timing -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn crossover() {
        use curve25519_dalek::scalar::Scalar;
        use subtle::{Choice, ConstantTimeEq};
        for &(t, q) in &[(16usize, 64usize), (256, 64), (256, 256), (256, 4096), (4096, 1024), (65536, 4096)] {
            let rows: Vec<Vec<u8>> = (0..t as u64).map(|i| Scalar::from(i).to_bytes().to_vec()).collect();
            let lookups: Vec<Vec<u8>> = (0..q as u64).map(|i| Scalar::from((i * 7919) % t as u64).to_bytes().to_vec()).collect();
            let s = std::time::Instant::now();
            let (m, _) = super::count(&rows, &lookups);
            let sort = s.elapsed();
            let direct = if (t * q) <= 1 << 24 {
                let rs: Vec<Scalar> = (0..t as u64).map(Scalar::from).collect();
                let qs: Vec<Scalar> = (0..q as u64).map(|i| Scalar::from((i * 7919) % t as u64)).collect();
                let s = std::time::Instant::now();
                let mut mm = vec![0u64; t];
                for x in &qs {
                    let mut found = Choice::from(0u8);
                    for (r, y) in rs.iter().enumerate() {
                        let eq = x.ct_eq(y);
                        mm[r] += (eq & !found).unwrap_u8() as u64;
                        found |= eq;
                    }
                }
                assert_eq!(mm, m);
                format!("{:?}", s.elapsed())
            } else {
                "-".into()
            };
            println!("|T| = {:6}, |Q| = {:5}: sort {:?}, direct {}", t, q, sort, direct);
        }
    }
}

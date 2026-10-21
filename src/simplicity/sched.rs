//! The order of a program's steps: greedy list scheduling that keeps few bits live, since
//! every step copies the values still needed.

/// The steps of a program as a DAG: each root's dependencies (the roots its expression reads)
/// and the bits its value takes in the environment.
pub(crate) struct Graph {
    pub deps: Vec<Vec<usize>>,
    pub bits: Vec<u64>,
    readers: Vec<Vec<usize>>,
}

impl Graph {
    /// A graph from each root's dependencies (earlier roots, in program order) and widths.
    pub(crate) fn new(deps: Vec<Vec<usize>>, bits: Vec<u64>) -> Self {
        let mut deps: Vec<Vec<usize>> = deps;
        for d in deps.iter_mut() {
            d.sort_unstable();
            d.dedup();
        }
        let mut readers = vec![Vec::new(); deps.len()];
        for (r, ds) in deps.iter().enumerate() {
            for d in ds {
                readers[*d].push(r);
            }
        }
        Graph { deps, bits, readers }
    }

    /// The number of roots.
    pub(crate) fn len(&self) -> usize {
        self.deps.len()
    }
}

/// Σ over steps of the bits live after the step (values with readers still to come): the
/// copying a program in this order does.
pub(crate) fn live_bits(g: &Graph, order: &[usize]) -> u64 {
    let mut left: Vec<usize> = g.readers.iter().map(|r| r.len()).collect();
    let mut live = 0u64;
    let mut total = 0u64;
    for &r in order {
        for &d in &g.deps[r] {
            left[d] -= 1;
            if left[d] == 0 {
                live -= g.bits[d];
            }
        }
        if left[r] > 0 {
            live += g.bits[r];
        }
        total += live;
    }
    total
}

/// Greedy list scheduling: of the ready roots, the one whose step changes the live bits least
/// (bits it adds, if read later, minus bits of the values it reads for the last time); ties to
/// the earlier root. The program order is kept if the greedy order is not better.
pub(crate) fn schedule(g: &Graph) -> Vec<usize> {
    let n = g.len();
    let mut pending: Vec<usize> = g.deps.iter().map(|d| d.len()).collect();
    let mut left: Vec<usize> = g.readers.iter().map(|r| r.len()).collect();
    let mut ready: std::collections::BTreeSet<usize> = (0..n).filter(|r| pending[*r] == 0).collect();
    let mut order = Vec::with_capacity(n);
    while let Some(&first) = ready.iter().next() {
        let mut best = (i64::MAX, first);
        for &r in &ready {
            let added = if left[r] > 0 { g.bits[r] as i64 } else { 0 };
            let freed: i64 = g.deps[r].iter().filter(|d| left[**d] == 1).map(|d| g.bits[*d] as i64).sum();
            let delta = added - freed;
            if delta < best.0 {
                best = (delta, r);
            }
        }
        let r = best.1;
        ready.remove(&r);
        order.push(r);
        for &d in &g.deps[r] {
            left[d] -= 1;
        }
        for &x in &g.readers[r] {
            pending[x] -= 1;
            if pending[x] == 0 {
                ready.insert(x);
            }
        }
    }
    let program: Vec<usize> = (0..n).collect();
    if live_bits(g, &order) <= live_bits(g, &program) {
        order
    } else {
        program
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A random DAG of roots: each reads up to three earlier ones.
    fn random_graph(seed: u64, n: usize) -> Graph {
        let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        let mut rnd = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let deps: Vec<Vec<usize>> = (0..n).map(|i| if i == 0 { vec![] } else { (0..(rnd() % 4)).map(|_| (rnd() as usize) % i).collect() }).collect();
        let bits = (0..n).map(|i| if i % 5 == 0 { 768 } else { 256 }).collect();
        Graph::new(deps, bits)
    }

    #[test]
    fn schedule_is_topological() {
        for seed in 1..20 {
            let g = random_graph(seed, 60);
            let order = schedule(&g);
            let mut pos = vec![usize::MAX; g.len()];
            for (k, r) in order.iter().enumerate() {
                pos[*r] = k;
            }
            assert!(pos.iter().all(|p| *p != usize::MAX), "every root is scheduled once");
            for r in 0..g.len() {
                for d in &g.deps[r] {
                    assert!(pos[*d] < pos[r], "seed {}: {} before its dependency {}", seed, r, d);
                }
            }
        }
    }

    #[test]
    fn schedule_is_deterministic() {
        let g = random_graph(7, 80);
        assert_eq!(schedule(&g), schedule(&g));
    }

    #[test]
    fn schedule_not_worse_than_program_order() {
        for seed in 1..20 {
            let g = random_graph(seed, 60);
            let ir: Vec<usize> = (0..g.len()).collect();
            assert!(live_bits(&g, &schedule(&g)) <= live_bits(&g, &ir), "seed {}", seed);
        }
    }

    /// Two independent chains of "term" steps, each with a value that lives until its term:
    /// interleaving them badly keeps both alive; the scheduler finishes one first.
    #[test]
    fn schedule_finishes_what_it_starts() {
        // 0, 1: long-lived values (512 bits each); 2 reads 0; 3 reads 1; 4 reads 2, 3
        let g = Graph::new(vec![vec![], vec![], vec![0], vec![1], vec![2, 3]], vec![512, 512, 256, 256, 768]);
        let order = schedule(&g);
        assert!(live_bits(&g, &order) <= live_bits(&g, &[0, 1, 2, 3, 4]));
        assert_eq!(order, vec![0, 2, 1, 3, 4]);
    }
}

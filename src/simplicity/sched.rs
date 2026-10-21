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

/// The order of the three below with the fewest live bits (ties to the earlier candidate):
/// on demand, greedy, the program's own.
pub(crate) fn schedule(g: &Graph) -> Vec<usize> {
    let program: Vec<usize> = (0..g.len()).collect();
    let mut best = program;
    let mut best_bits = live_bits(g, &best);
    for order in [on_demand(g), greedy(g)] {
        let b = live_bits(g, &order);
        if b < best_bits {
            best = order;
            best_bits = b;
        }
    }
    best
}

/// Scheduling on demand: from each sink (a root nobody reads: a check, the last term of a sum)
/// in program order, the roots it needs depth first (deepest first), then the sink. A term of a sum is computed
/// right after its own inputs, so vectors built in loops die term by term.
fn on_demand(g: &Graph) -> Vec<usize> {
    let n = g.len();
    // the deepest dependency first (Sethi–Ullman): a chain of terms before the small values
    // a term reads, so that those are computed right before it
    let mut height = vec![0usize; n];
    for r in 0..n {
        height[r] = g.deps[r].iter().map(|d| height[*d] + 1).max().unwrap_or(0);
    }
    let by_depth: Vec<Vec<usize>> = g
        .deps
        .iter()
        .map(|ds| {
            let mut v = ds.clone();
            v.sort_by(|a, b| height[*b].cmp(&height[*a]).then(a.cmp(b)));
            v
        })
        .collect();
    let mut done = vec![false; n];
    let mut order = Vec::with_capacity(n);
    for sink in (0..n).filter(|r| g.readers[*r].is_empty()) {
        // iterative depth-first post-order (chains of terms are long)
        let mut stack: Vec<(usize, usize)> = vec![(sink, 0)];
        while let Some(&mut (r, ref mut next)) = stack.last_mut() {
            if done[r] {
                stack.pop();
                continue;
            }
            if *next < by_depth[r].len() {
                let d = by_depth[r][*next];
                *next += 1;
                if !done[d] {
                    stack.push((d, 0));
                }
            } else {
                done[r] = true;
                order.push(r);
                stack.pop();
            }
        }
    }
    order
}

/// Greedy list scheduling: of the ready roots, the one whose step changes the live bits least
/// (bits it adds, if read later, minus bits of the values it reads for the last time); ties to
/// the earlier root.
fn greedy(g: &Graph) -> Vec<usize> {
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
    order
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

    /// Vectors computed in loops, then combined term by term: `a_i` (roots 0..n), `b_i`
    /// (n..2n), term `t_i` reads `a_i`, `b_i` and `t_{i-1}`. The program order keeps every
    /// `a_i` alive until its term; scheduling on demand computes `a_i, b_i, t_i` together.
    #[test]
    fn schedule_fuses_vectors_with_their_terms() {
        let n = 30;
        let mut deps: Vec<Vec<usize>> = vec![vec![]; 2 * n];
        let mut bits = vec![256u64; 2 * n];
        for i in 0..n {
            let mut d = vec![i, n + i];
            if i > 0 {
                d.push(2 * n + i - 1);
            }
            deps.push(d);
            bits.push(768);
        }
        let g = Graph::new(deps, bits);
        let order = schedule(&g);
        let program: Vec<usize> = (0..g.len()).collect();
        assert!(live_bits(&g, &order) * 5 < live_bits(&g, &program), "{} vs {}", live_bits(&g, &order), live_bits(&g, &program));
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

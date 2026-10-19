# Errata 19: is the circuit protocol still zero-knowledge when C_O is dropped (r_O = 0), as
# the paper's §6.4.2 says for shared multiplicities? Rank of the map from the prover's blinding
# randomness to the opening's blinding part r(tau) (spec §3.6-3.7; r_S solved from d = f - g,
# f does not depend on r_O, r_L, r_R), alone and jointly with what C_L, C_R (, C_O) reveal
# about their blinding (generic linear functionals). Run: python3 -I ref/checks/drop_co_zk_rank.py
import random
P = 2**252 + 27742317777372353535851937790883648493
E = [-1, 1, 2, 3, 5, 6, 7]
inv = lambda x: pow(x, P - 2, P)
def r_tau(rO, rL, rR, beta, delta, tau):
    # g(T) = sum_X sum_j beta T^{e_j} sigma r_{X,j} - sigma r_{X,0}; sigma: O->delta, L->T, R->T^2
    g = {}
    def add(d, v): g[d] = (g.get(d, 0) + v) % P
    for r, deg, s in ((rO, 0, delta), (rL, 1, 1), (rR, 2, 1)):
        add(deg, -s * r[0])
        for j, e in enumerate(E):
            add(deg + e, beta * s * r[j + 1])
    d = {k: -v % P for k, v in g.items()}       # d = f - g with f = 0 (offset only)
    rS = [(-d.get(-1, 0)) % P] + [inv(beta) * d.get(e - 1, 0) % P for e in E]
    ti = inv(tau)
    return [(ti * rS[j] + delta * rO[j] + tau * rL[j] + tau * tau * rR[j]) % P for j in range(8)]
def rank(rows):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % P), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = inv(rows[rk][c])
        rows[rk] = [x * iv % P for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % P:
                f = rows[i][c]; rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk
O_IDX = [0, 1, 2, 3, 5, 6]; L_IDX = [0, 1, 2, 4, 5]; R_IDX = [0, 1, 3, 4]
for with_O in (True, False):
    ranks = set()
    for _ in range(20):
        beta, delta, tau = (random.randrange(1, P) for _ in range(3))
        cols = []
        for name, idx in (("O", O_IDX if with_O else []), ("L", L_IDX), ("R", R_IDX)):
            for k in idx:
                z = [0] * 8
                vec = {"O": z[:], "L": z[:], "R": z[:]}
                vec[name][k] = 1
                cols.append(r_tau(vec["O"], vec["L"], vec["R"], beta, delta, tau))
        # also the constraint <c_r(tau), (r_1..7)> + ... : check the opening coordinates' span
        ranks.add(rank(cols))
    print("with C_O" if with_O else "without C_O", "rank of (r_O, r_L, r_R) -> r(tau):", ranks)

# Joint: the opening (8 coordinates of r(tau)) together with what the points C_O, C_L, C_R
# reveal about their blinding: x . r_X for ONE vector x of discrete logs (the three commitments
# use the same generators G, H_0..H_6). Random challenges, then special ones.
def joint(with_O, beta, delta, tau, x):
    rows = []
    for name, idx in (("O", O_IDX if with_O else []), ("L", L_IDX), ("R", R_IDX)):
        for k in idx:
            vec = {"O": [0] * 8, "L": [0] * 8, "R": [0] * 8}
            vec[name][k] = 1
            rt = r_tau(vec["O"], vec["L"], vec["R"], beta, delta, tau)
            fs = [sum(a * b for a, b in zip(x, vec[X])) % P for X in (("O", "L", "R") if with_O else ("L", "R"))]
            rows.append(rt + fs)
    return rank(rows)

for with_O in (True, False):
    need = 7 + (3 if with_O else 2)
    ranks = {joint(with_O, *(random.randrange(1, P) for _ in range(3)), [random.randrange(P) for _ in range(8)]) for _ in range(20)}
    special = [1, P - 1, 2, P - 2, 3, inv(2), inv(3)] + list(range(4, 9))
    low = [(b, d, t) for b in special for d in special for t in special[:7]
           if joint(with_O, b, d, t, [random.randrange(P) for _ in range(8)]) < need]
    print("with C_O" if with_O else "without C_O", "joint rank", ranks, "needed", need, "special challenges below:", len(low))

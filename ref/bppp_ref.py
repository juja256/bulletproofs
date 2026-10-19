#!/usr/bin/env python3
"""Spec-level reference of the BP++ protocols, written from docs/bppp/spec.md and the paper
(ePrint 2022/510), not from the Rust code.

Pure field arithmetic modulo the ristretto255 group order. Group elements are symbolic: a
point is a map {generator: coefficient} over the named base generators ("G", 0), ("H", i)
and ("N", i). Challenges are inputs, so the vectors check the protocol algebra; Fiat-Shamir
and point encoding are checked separately (transcript tests in Rust).
"""

import random

L = 2**252 + 27742317777372353535851937790883648493


def use_field(modulus):
    """Switch the scalar field (the secp256k1-zkp cross-check runs the same code over the
    secp256k1 group order)."""
    global L
    L = modulus


def inv(x):
    assert x % L != 0
    return pow(x, L - 2, L)


class Sym:
    """A group element as a linear combination of named base generators."""

    def __init__(self, d=None):
        self.d = {}
        for k, v in (d or {}).items():
            v %= L
            if v:
                self.d[k] = v

    @staticmethod
    def gen(name, i=0):
        return Sym({(name, i): 1})

    def __add__(self, o):
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return Sym(d)

    def __sub__(self, o):
        return self + o.scale(L - 1)

    def scale(self, s):
        return Sym({k: v * s for k, v in self.d.items()})

    def __eq__(self, o):
        return self.d == o.d

    def coeffs(self, a, b):
        """Dense coefficients over (G, H[0..a), N[0..b)) for the vector files."""
        g = self.d.get(("G", 0), 0)
        h = [self.d.get(("H", i), 0) for i in range(a)]
        n = [self.d.get(("N", i), 0) for i in range(b)]
        assert len(self.d) == (g != 0) + sum(x != 0 for x in h) + sum(x != 0 for x in n)
        return g, h, n


ZERO = Sym()


def msm(scalars, points, zero=ZERO):
    acc = zero
    for s, p in zip(scalars, points):  # zip = implicit zero padding of the shorter side
        acc = acc + p.scale(s)
    return acc


def ip(a, b):
    return sum(x * y for x, y in zip(a, b)) % L


def wip(a, b, mu):
    """Weighted inner product <a, b>_mu = sum a_i b_i mu^(i+1) (paper, section 2)."""
    acc, w = 0, mu
    for x, y in zip(a, b):
        acc = (acc + x * y * w) % L
        w = w * mu % L
    return acc


def split(v):
    """Even and odd components [v]_0, [v]_1 (paper, section 2)."""
    return v[0::2], v[1::2]


def fold(v0, v1, e, g):
    """e*[v]_0 + g*[v]_1, zero-padded on the right: len = len(v0) = ceil(len(v)/2)."""
    return [(e * x + g * (v1[i] if i < len(v1) else 0)) % L for i, x in enumerate(v0)]


def fold_pts(p0, p1, e, g):
    return [x.scale(e) + p1[i].scale(g) if i < len(p1) else x.scale(e) for i, x in enumerate(p0)]


def wnla_more(a, b, legacy=False):
    """Whether to fold once more (spec section 2.2). Default: only if the round removes at
    least 3 scalars, the size-optimal layout of secp256k1-zkp PR #352. Legacy: fold down to
    single scalars, as secp256k1-zkp master does (power-of-two lengths)."""
    return (a > 1 or b > 1) if legacy else a // 2 + b // 2 >= 3


def wnla_rounds(a, b, legacy=False):
    """(rounds, final |l|, final |n|) for |l| = a, |n| = b."""
    k = 0
    while wnla_more(a, b, legacy):
        a, b, k = (a + 1) // 2, (b + 1) // 2, k + 1
    return k, a, b


def wnla_commit(G, H, N, c, mu, l, n):
    v = (ip(c, l) + wip(n, n, mu)) % L
    zero = G.scale(0)
    return G.scale(v) + msm(l, H, zero) + msm(n, N, zero)


def wnla_prove(G, H, N, c, rho, l, n, challenge, legacy=False):
    """Prover of the weighted norm linear argument (section 4.3). `challenge(X, R)` returns
    the round challenge (a list iterator for the vectors, a transcript for the cross-check).
    A norm vector of length 1 is not folded and rho, mu stay (secp256k1-zkp).
    Returns ([(X, R)], l_final, n_final)."""
    zero = G.scale(0)
    mu = rho * rho % L
    rounds = []
    while wnla_more(len(l), len(n), legacy):
        rho_inv = inv(rho)
        mu2 = mu * mu % L
        l0, l1 = split(l)
        n0, n1 = split(n)
        c0, c1 = split(c)
        H0, H1 = split(H)
        N0, N1 = split(N)
        vx = (2 * rho_inv * wip(n0, n1, mu2) + ip(c0, l1) + ip(c1, l0)) % L
        vr = (wip(n1, n1, mu2) + ip(c1, l1)) % L
        X = (G.scale(vx) + msm(l1, H0, zero) + msm(l0, H1, zero)
             + msm([rho * x for x in n1], N0, zero) + msm([rho_inv * x for x in n0], N1, zero))
        R = G.scale(vr) + msm(l1, H1, zero) + msm(n1, N1, zero)
        rounds.append((X, R))
        gamma = challenge(X, R)
        if len(l) > 1:
            c = fold(c0, c1, 1, gamma)
            l = fold(l0, l1, 1, gamma)
            H = fold_pts(H0, H1, 1, gamma)
        if len(n) > 1:
            n = fold(n0, n1, rho_inv, gamma)
            N = fold_pts(N0, N1, rho, gamma)
            rho, mu = mu, mu2
    return rounds, l, n


def wnla_verify(G, H, N, c, rho, C, rounds, l, n, gammas, legacy=False):
    """Naive recursive verifier (section 4.3): fold everything, check the opening."""
    mu = rho * rho % L
    k, a, b = wnla_rounds(len(H), len(N), legacy)
    if len(rounds) != k or len(l) != a or len(n) != b or len(gammas) != k:
        return False
    for (X, R), gamma in zip(rounds, gammas):
        c0, c1 = split(c)
        H0, H1 = split(H)
        N0, N1 = split(N)
        C = C + X.scale(gamma) + R.scale(gamma * gamma - 1)
        if len(H) > 1:
            c = fold(c0, c1, 1, gamma)
            H = fold_pts(H0, H1, 1, gamma)
        if len(N) > 1:
            N = fold_pts(N0, N1, rho, gamma)
            rho, mu = mu, mu * mu % L
    return C == wnla_commit(G, H, N, c, mu, l, n)


# ---------------------------------------------------------------------------------------------
# Arithmetic circuits (spec section 3, paper section 5)
#
# Laurent polynomials in T: a scalar polynomial is a dict {degree: coefficient}, a vector
# polynomial a dict {degree: list of scalars} (all lists of one polynomial have equal length).
# Zero coefficients are dropped, so the keys are exactly the support.


def lp_norm(p):
    return {e: x % L for e, x in p.items() if x % L}


def lp_add(*ps):
    acc = {}
    for p in ps:
        for e, x in p.items():
            acc[e] = acc.get(e, 0) + x
    return lp_norm(acc)


def lp_scale(p, s):
    return lp_norm({e: x * s for e, x in p.items()})


def lp_mul(a, b):
    acc = {}
    for e, x in a.items():
        for f, y in b.items():
            acc[e + f] = acc.get(e + f, 0) + x * y
    return lp_norm(acc)


def tpow(x, e):
    """x^e for any integer e (x != 0 if e < 0)."""
    return pow(x, e, L) if e >= 0 else pow(inv(x), -e, L)


def lp_eval(p, x):
    return sum(c * tpow(x, e) for e, c in p.items()) % L


def vp_norm(p):
    out = {}
    for e, v in p.items():
        v = [x % L for x in v]
        if any(v):
            out[e] = v
    return out


def vp_add(n, *ps):
    acc = {}
    for p in ps:
        for e, v in p.items():
            assert len(v) == n
            a = acc.setdefault(e, [0] * n)
            for i, x in enumerate(v):
                a[i] += x
    return vp_norm(acc)


def vp_ip(a, b):
    """<a(T), b(T)> as a scalar polynomial."""
    acc = {}
    for e, x in a.items():
        for f, y in b.items():
            acc[e + f] = acc.get(e + f, 0) + ip(x, y)
    return lp_norm(acc)


def vp_wip(a, b, mu):
    """<a(T), b(T)>_mu as a scalar polynomial."""
    acc = {}
    for e, x in a.items():
        for f, y in b.items():
            acc[e + f] = acc.get(e + f, 0) + wip(x, y, mu)
    return lp_norm(acc)


def vp_eval(p, x, n):
    out = [0] * n
    for e, v in p.items():
        xe = tpow(x, e)
        for i, y in enumerate(v):
            out[i] = (out[i] + y * xe) % L
    return out


# Exponents of c_r(T) = beta (T^-1, T, T^2, T^3, T^5, T^6, T^7) (section 3.5/3.6).
CR_EXP = (-1, 1, 2, 3, 5, 6, 7)
SLOTS = ("nO", "lO", "lL", "lR")


def circuit_gens(c):
    """Section 3.2: G, H (|H| = 7 + N_lin; H_0 = input blinding, H_1..6 the remaining blinding
    slots, H_7.. the linear part), N (|N| = N_m), as symbolic generators."""
    return (Sym.gen("G"), [Sym.gen("H", i) for i in range(7 + c["n_lin"])],
            [Sym.gen("N", t) for t in range(c["n_m"])])


def circuit_check_shape(c):
    nm, no, nv, nlin, k, nl = (c[x] for x in ("n_m", "n_o", "n_v", "n_lin", "k", "n_l"))
    assert nm >= 1 and nv >= 1 and k >= 0 and nlin >= nv - 1
    assert len(c["w_l"]) == nl == len(c["a_l"]) and len(c["w_m"]) == nm == len(c["a_m"])
    assert not c["f_l"] or nl >= k * nv
    assert not c["f_m"] or nm >= k * nv
    assert k == 0 or c["f_l"] or c["f_m"], "inputs must enter some constraint (spec 3.1)"
    assert len(c["partition"]) == no
    assert len(set(map(tuple, c["partition"]))) == no  # injective
    for slot, t in c["partition"]:
        assert slot in SLOTS and 0 <= t < (nm if slot == "nO" else nlin)
    for row in c["w_l"] + c["w_m"]:
        for col, _ in row:
            assert 0 <= col < 2 * nm + no


def sparse_mul(rows, w):
    return [sum(x * w[col] for col, x in row) % L for row in rows]


def circuit_error(c, wit, lam, mu):
    """E of section 3.5 (with the weights Lambda of 3.4), from the relation directly.
    Returns (E, satisfied)."""
    nm, nl = c["n_m"], c["n_l"]
    w = wit["w_L"] + wit["w_R"] + wit["w_O"]
    wv = [x for v in wit["v"] for x in v]
    lin = [(x + c["f_l"] * (wv[t] if t < len(wv) else 0) + c["a_l"][t]) % L
           for t, x in enumerate(sparse_mul(c["w_l"], w))]
    mul = [(x + c["f_m"] * (wv[t] if t < len(wv) else 0) + c["a_m"][t]) % L
           for t, x in enumerate(sparse_mul(c["w_m"], w))]
    hadamard = [x * y % L for x, y in zip(wit["w_L"], wit["w_R"])]
    satisfied = all(x == 0 for x in lin) and hadamard == mul
    Lam = circuit_lambda(c, lam, mu)
    mus = [pow(mu, r + 1, L) for r in range(nm)]
    E = (ip(Lam, lin) + wip(wit["w_L"], wit["w_R"], mu) - ip(mus, mul)) % L
    assert len(Lam) == nl
    return E, satisfied


def circuit_lambda(c, lam, mu):
    """Linear weights Lambda (section 3.4)."""
    nv, k = c["n_v"], c["k"]
    Lam = [pow(lam, t, L) for t in range(c["n_l"])]
    if c["f_l"] and c["f_m"]:
        for i in range(k):
            for j in range(1, nv):
                t = nv * i + j
                Lam[t] = (pow(lam, t, L) + pow(mu, j, L) * pow(lam, nv * i, L)
                          - pow(lam, j, L) * pow(mu, nv * i + 1, L)) % L
    return Lam


def circuit_public(c, chal):
    """Everything the verifier derives from the circuit and the challenges (sections 3.4, 3.5):
    weights, input scalings and the public Laurent polynomials p_n, p_s, c_l_hat, c_r."""
    nm, no, nv, nlin, k = (c[x] for x in ("n_m", "n_o", "n_v", "n_lin", "k"))
    fl, fm = c["f_l"], c["f_m"]
    rho, lam, beta, delta = chal["rho"], chal["lambda"], chal["beta"], chal["delta"]
    mu = rho * rho % L
    mus = [pow(mu, r + 1, L) for r in range(nm)]
    Lam = circuit_lambda(c, lam, mu)
    # y = Lambda^T W_l - mu^T W_m
    y = [0] * (2 * nm + no)
    for row, wt in zip(c["w_l"], Lam):
        for col, x in row:
            y[col] += wt * x
    for row, wt in zip(c["w_m"], mus):
        for col, x in row:
            y[col] -= wt * x
    y = [x % L for x in y]
    c_n = {"nL": [y[t] * inv(mus[t]) % L for t in range(nm)],
           "nR": [y[nm + t] * inv(mus[t]) % L for t in range(nm)],
           "nO": [0] * nm}
    c_l = {"lO": [0] * nlin, "lL": [0] * nlin, "lR": [0] * nlin}
    for i, (slot, t) in enumerate(c["partition"]):
        if slot == "nO":
            c_n["nO"][t] = y[2 * nm + i] * inv(mus[t]) % L
        else:
            c_l[slot][t] = y[2 * nm + i]
    nu = [2 * (fm * pow(mu, nv * i + 1, L) - fl * pow(lam, nv * i, L)) % L for i in range(k)]
    c_V = [-(fm * pow(mu, j, L) + fl * pow(lam, j, L)) % L for j in range(1, nv)]
    c_V += [0] * (nlin - len(c_V))
    di = inv(delta)
    p_n = vp_norm({3: [di * x for x in c_n["nO"]], 2: c_n["nL"], 1: c_n["nR"]})
    p_s = lp_add(vp_wip(p_n, p_n, mu),
                 {3: 2 * ip(mus, c["a_m"]) - 2 * ip(Lam, c["a_l"])})
    c_l_hat = vp_norm({3: [2 * di * x for x in c_l["lO"]], 2: [2 * x for x in c_l["lL"]],
                       1: [2 * x for x in c_l["lR"]], 0: c_V})
    c_r = {}
    for j, e in enumerate(CR_EXP):
        c_r[e] = [beta if i == j else 0 for i in range(7)]
    return {"mu": mu, "mus": mus, "Lambda": Lam, "y": y, "c_n": c_n, "c_l": c_l, "nu": nu,
            "c_V": c_V, "p_n": p_n, "p_s": p_s, "c_l_hat": c_l_hat, "c_r": vp_norm(c_r)}


def circuit_layout(c, wit):
    """Section 3.3: n_O, l_O, l_L, l_R from the partition."""
    nm, nlin = c["n_m"], c["n_lin"]
    slots = {"nO": [0] * nm, "lO": [0] * nlin, "lL": [0] * nlin, "lR": [0] * nlin}
    for x, (slot, t) in zip(wit["w_O"], c["partition"]):
        slots[slot][t] = x
    return slots


def circuit_commit(G, H, N, r, l, n):
    """C_X = r_0 G + sum_{j=1..7} r_j H_{j-1} + <l, H_7..> + <n, N> (section 3.3)."""
    assert len(r) == 8 and len(l) == len(H) - 7 and len(n) == len(N)
    return G.scale(r[0]) + msm(r[1:], H[:7]) + msm(l, H[7:]) + msm(n, N)


def circuit_input_commit(G, H, v, s):
    """V_i = v_0 G + s H_0 + sum_{j>=1} v_j H_{6+j} (section 3.2)."""
    return G.scale(v[0]) + H[0].scale(s) + msm(v[1:], H[7:])


def circuit_blindings(rnd):
    """r_O, r_L, r_R of section 3.3 from r'_O (6), r'_L (5), r'_R (4)."""
    ro, rl, rr = rnd["r_O"], rnd["r_L"], rnd["r_R"]
    assert len(ro) == 6 and len(rl) == 5 and len(rr) == 4
    return ([ro[0], ro[1], ro[2], ro[3], 0, ro[4], ro[5], 0],
            [rl[0], rl[1], rl[2], 0, rl[3], rl[4], 0, 0],
            [rr[0], rr[1], 0, rr[2], rr[3], 0, 0, 0])


def circuit_commit_initial(c, wit, rnd):
    """(C_L, C_O) of section 3.3. Reads only w_L and the elements of w_O in the slots n_O, l_O,
    l_L (the reciprocal form commits these before alpha, spec 4.3)."""
    G, H, N = circuit_gens(c)
    lay = circuit_layout(c, wit)
    r_O, r_L, _ = circuit_blindings(rnd)
    return (circuit_commit(G, H, N, r_L, lay["lL"], wit["w_L"]),
            circuit_commit(G, H, N, r_O, lay["lO"], lay["nO"]))


def circuit_commit_right(c, wit, rnd):
    """C_R of section 3.3 (w_R and the l_R elements of w_O)."""
    G, H, N = circuit_gens(c)
    lay = circuit_layout(c, wit)
    _, _, r_R = circuit_blindings(rnd)
    return circuit_commit(G, H, N, r_R, lay["lR"], wit["w_R"])


def circuit_prove(c, wit, rnd, chal, gammas):
    """Prover of section 3 with given randomness and challenges (no transcript). Returns a dict
    with everything the prover sends, the norm-argument inputs and the intermediate polynomials
    (for the self-checks)."""
    circuit_check_shape(c)
    nm, no, nv, nlin, k = (c[x] for x in ("n_m", "n_o", "n_v", "n_lin", "k"))
    assert len(wit["w_L"]) == nm == len(wit["w_R"]) and len(wit["w_O"]) == no
    assert len(wit["v"]) == k == len(wit["s"]) and all(len(v) == nv for v in wit["v"])
    G, H, N = circuit_gens(c)
    rho, beta, delta, tau = chal["rho"], chal["beta"], chal["delta"], chal["tau"]
    assert all(x % L for x in (rho, beta, delta, tau))

    # 3.2, 3.3: input commitments and C_L, C_R, C_O
    V = [circuit_input_commit(G, H, v, s) for v, s in zip(wit["v"], wit["s"])]
    lay = circuit_layout(c, wit)
    r_O, r_L, r_R = circuit_blindings(rnd)
    n_L, n_R, n_O = wit["w_L"], wit["w_R"], lay["nO"]
    l_O, l_L, l_R = lay["lO"], lay["lL"], lay["lR"]
    C_L, C_O = circuit_commit_initial(c, wit, rnd)
    C_R = circuit_commit_right(c, wit, rnd)

    # 3.4: weights and inputs
    pub = circuit_public(c, chal)
    mu, nu = pub["mu"], pub["nu"]
    v_hat = sum(x * v[0] for x, v in zip(nu, wit["v"])) % L
    l_V = [sum(x * v[j] for x, v in zip(nu, wit["v"])) % L for j in range(1, nv)]
    l_V += [0] * (nlin - len(l_V))
    r_V = [0, sum(x * s for x, s in zip(nu, wit["s"])) % L, 0, 0, 0, 0, 0, 0]

    # 3.5: polynomials
    l_S, n_S = rnd["l_S"], rnd["n_S"]
    assert len(l_S) == nlin and len(n_S) == nm
    l_hat = vp_norm({-1: l_S, 0: [delta * x for x in l_O], 1: l_L, 2: l_R, 3: l_V})
    n_hat = vp_norm({-1: n_S, 0: [delta * x for x in n_O], 1: n_L, 2: n_R})
    n_poly = vp_add(nm, pub["p_n"], n_hat)
    f_hat = lp_add(pub["p_s"], {3: v_hat}, lp_scale(vp_ip(pub["c_l_hat"], l_hat), -1),
                   lp_scale(vp_wip(n_poly, n_poly, mu), -1))

    # 3.6: blinding commitment
    sigma = {"O": {0: delta}, "L": {1: 1}, "R": {2: 1}, "V": {3: 1}}
    rX = {"O": r_O, "L": r_L, "R": r_R, "V": r_V}
    g = {}
    for X in ("O", "L", "R", "V"):
        inner = lp_add(vp_ip(pub["c_r"], {0: rX[X][1:]}), {0: -rX[X][0]})
        g = lp_add(g, lp_mul(sigma[X], inner))
    d = lp_add(f_hat, lp_scale(g, -1))
    r_S = [-d.get(-1, 0) % L] + [inv(beta) * d.get(e - 1, 0) % L for e in CR_EXP]
    C_S = circuit_commit(G, H, N, r_S, l_S, n_S)

    # 3.7: opening at tau and the norm argument
    r_poly = vp_norm({-1: r_S, 0: [delta * x for x in r_O], 1: r_L, 2: r_R, 3: r_V})
    r_tau = vp_eval(r_poly, tau, 8)
    v = (lp_eval(pub["p_s"], tau) + r_tau[0] + pow(tau, 3, L) * v_hat) % L
    wl = r_tau[1:] + vp_eval(l_hat, tau, nlin)
    wn = vp_eval(n_poly, tau, nm)
    wc = vp_eval(pub["c_r"], tau, 7) + vp_eval(pub["c_l_hat"], tau, nlin)
    gi = iter(gammas)
    rounds, l_final, n_final = wnla_prove(G, H, N, wc, rho, list(wl), list(wn),
                                          lambda X, R: next(gi))
    assert next(gi, None) is None, "unused gammas"
    # g with the r_S part, <c_r(T), r_{1:}(T)> - r_0(T), for the self-checks
    g_full = lp_add(vp_ip(pub["c_r"], {e: x[1:] for e, x in r_poly.items()}),
                    lp_scale({e: x[0] for e, x in r_poly.items()}, -1))
    return {"V": V, "C_L": C_L, "C_R": C_R, "C_O": C_O, "C_S": C_S,
            "r_O": r_O, "r_L": r_L, "r_R": r_R, "r_V": r_V, "r_S": r_S,
            "v_hat": v_hat, "l_V": l_V, "pub": pub,
            "f_hat": f_hat, "g": g, "g_full": g_full, "d": d,
            "wnla_v": v, "wnla_c": wc, "wnla_l": wl, "wnla_n": wn,
            "rounds": rounds, "l_final": l_final, "n_final": n_final}


def circuit_commitment(c, chal, V, C_L, C_R, C_O, C_S):
    """The verifier's C(tau) and c (section 3.7)."""
    G, H, N = circuit_gens(c)
    pub = circuit_public(c, chal)
    tau, delta = chal["tau"], chal["delta"]
    t3 = pow(tau, 3, L)
    C = (G.scale(lp_eval(pub["p_s"], tau)) + msm(vp_eval(pub["p_n"], tau, c["n_m"]), N)
         + C_S.scale(inv(tau)) + C_O.scale(delta) + C_L.scale(tau) + C_R.scale(tau * tau)
         + msm([t3 * x for x in pub["nu"]], V))
    wc = vp_eval(pub["c_r"], tau, 7) + vp_eval(pub["c_l_hat"], tau, c["n_lin"])
    return C, wc, pub


def circuit_verify(c, V, C_L, C_R, C_O, C_S, chal, rounds, l_final, n_final, gammas):
    """Verifier of section 3.7 via C(tau) and the naive norm-argument verifier."""
    if any(chal[x] % L == 0 for x in ("rho", "beta", "delta", "tau")) or len(V) != c["k"]:
        return False
    G, H, N = circuit_gens(c)
    C, wc, _ = circuit_commitment(c, chal, V, C_L, C_R, C_O, C_S)
    return wnla_verify(G, H, N, wc, chal["rho"], C, rounds, l_final, n_final, gammas)


def wnla_verification_scalars(a, b, c, rho, gammas, l, n):
    """Section 2.4: (v, h, n') such that the proof is valid iff
    v G + <h, H> + <n', N> - C - sum_r (gamma_r X_r + (gamma_r^2 - 1) R_r) = 0."""
    k = len(gammas)
    ka = kn = 0  # rounds in which l (resp. n) was folded
    aa, bb = a, b
    for _ in range(k):
        if aa > 1:
            aa, ka = (aa + 1) // 2, ka + 1
        if bb > 1:
            bb, kn = (bb + 1) // 2, kn + 1
    assert len(l) == aa and len(n) == bb
    cc = list(c)
    for r, gamma in enumerate(gammas):
        if len(cc) > 1:
            c0, c1 = split(cc)
            cc = fold(c0, c1, 1, gamma)
    rho_r = [pow(rho, 2**r, L) if r < kn else 1 for r in range(k)]
    h = []
    for i in range(a):
        x = l[i >> k]
        for r in range(k):
            if (i >> r) & 1:
                x = x * gammas[r] % L
        h.append(x)
    nn = []
    for i in range(b):
        x = n[i >> k]
        for r in range(k):
            x = x * (gammas[r] if (i >> r) & 1 else rho_r[r]) % L
        nn.append(x)
    mu_fin = pow(rho, 2**(kn + 1), L)
    v = (ip(cc, l) + wip(n, n, mu_fin)) % L
    return v, h, nn


def circuit_verify_msm(c, V, C_L, C_R, C_O, C_S, chal, rounds, l_final, n_final, gammas):
    """Verifier of section 3.7 as the single multiscalar equation (with the scalars of 2.4)."""
    if any(chal[x] % L == 0 for x in ("rho", "beta", "delta", "tau")) or len(V) != c["k"]:
        return False
    a, b = 7 + c["n_lin"], c["n_m"]
    k, fa, fb = wnla_rounds(a, b)
    if len(rounds) != k or len(gammas) != k or len(l_final) != fa or len(n_final) != fb:
        return False
    G, H, N = circuit_gens(c)
    pub = circuit_public(c, chal)
    tau, delta = chal["tau"], chal["delta"]
    wc = vp_eval(pub["c_r"], tau, 7) + vp_eval(pub["c_l_hat"], tau, c["n_lin"])
    g, h, nn = wnla_verification_scalars(a, b, wc, chal["rho"], gammas, l_final, n_final)
    p_n = vp_eval(pub["p_n"], tau, b)
    t3 = pow(tau, 3, L)
    acc = (G.scale(g - lp_eval(pub["p_s"], tau)) + msm(h, H) + msm([x - y for x, y in zip(nn, p_n)], N)
           - C_S.scale(inv(tau)) - C_O.scale(delta) - C_L.scale(tau) - C_R.scale(tau * tau)
           - msm([t3 * x for x in pub["nu"]], V))
    for (X, R), gamma in zip(rounds, gammas):
        acc = acc - X.scale(gamma) - R.scale(gamma * gamma - 1)
    return acc == ZERO


def circuit_self_check(c, wit, chal, gammas, proof):
    """The self-checks: identity of 3.5, zero pattern of 3.6, opening and norm relation at tau,
    both verifiers. Returns (satisfied, verifies); raises AssertionError on any mismatch."""
    G, H, N = circuit_gens(c)
    pub = proof["pub"]
    E, satisfied = circuit_error(c, wit, chal["lambda"], pub["mu"])
    f_hat, g, g_full = proof["f_hat"], proof["g"], proof["g_full"]
    # 3.5 identity: the T^3 coefficient of f_hat is -2E (for any witness)
    assert f_hat.get(3, 0) == -2 * E % L, "f_hat_3 != -2E"
    assert (E == 0) == satisfied, "E vanishes on an unsatisfied witness (unlucky challenges)"
    # 3.6 zero pattern
    assert all(-2 <= e <= 6 for e in f_hat), f"f_hat degrees {sorted(f_hat)}"
    assert 3 not in g and all(-2 <= e <= 6 for e in g), f"g degrees {sorted(g)}"
    # r_S cancels every coefficient of f_hat - g_full except the value term
    assert lp_add(f_hat, lp_scale(g_full, -1)) == lp_norm({3: f_hat.get(3, 0)})
    # opening at tau: C(tau) the verifier's way = v G + <l, H> + <n, N>
    tau = chal["tau"]
    C, wc, _ = circuit_commitment(c, chal, proof["V"], proof["C_L"], proof["C_R"], proof["C_O"],
                                  proof["C_S"])
    assert wc == proof["wnla_c"]
    v, wl, wn = proof["wnla_v"], proof["wnla_l"], proof["wnla_n"]
    assert C == G.scale(v) + msm(wl, H) + msm(wn, N), "C(tau) != opening"
    # norm linear relation: v - <c, l> - |n|^2_mu = f_hat_3 tau^3, zero iff satisfied
    rel = (v - ip(wc, wl) - wip(wn, wn, pub["mu"])) % L
    assert rel == f_hat.get(3, 0) * pow(tau, 3, L) % L
    assert (rel == 0) == satisfied
    # full proof, both verifiers
    args = (c, proof["V"], proof["C_L"], proof["C_R"], proof["C_O"], proof["C_S"], chal,
            proof["rounds"], proof["l_final"], proof["n_final"], gammas)
    verifies = circuit_verify(*args)
    assert circuit_verify_msm(*args) == verifies, "the two verifiers disagree"
    assert verifies == satisfied
    return satisfied, verifies


# ---------------------------------------------------------------------------------------------
# Reciprocal form circuits (spec section 4, paper sections 6.2-6.3)
#
# A reciprocal form circuit rc has the keys of a section-3 circuit (n_m = N_m ordinary
# multiplications, which may be 0, w_m, a_m, w_l, a_l, n_o, n_v, n_lin, k, n_l, f_l, f_m,
# partition) plus n_p = N_p, w_n, a_n and recip: a list of rows {"terms": [(col, c, t)],
# "consts": [(c, t)]} with t None for "no pole". Columns index
# w' = w_D || w_L || w_P || w_R || w_O (N'_m = N_p + N_m). A witness has w_D, w_L, w_R, w_O,
# v, s; w_P is computed for a challenge alpha.


class ReciprocalError(Exception):
    """The prover fails (alpha + w_D,i = 0) or the circuit cannot be compiled for alpha
    (alpha + t = 0 for a public pole t)."""


def recip_dims(rc):
    """(N'_m, N'_w)."""
    nm2 = rc["n_p"] + rc["n_m"]
    return nm2, 2 * nm2 + rc["n_o"]


def recip_initial_cols(rc):
    """Columns committed before alpha (spec 4.1): all of w'_L = w_D || w_L, and the elements of
    w_O whose slot is not l_R."""
    nm2, _ = recip_dims(rc)
    cols = set(range(nm2))
    cols |= {2 * nm2 + i for i, (slot, _) in enumerate(rc["partition"]) if slot != "lR"}
    return cols


def recip_check_shape(rc):
    np_, nm, no, nv, nlin, k, nl = (rc[x] for x in ("n_p", "n_m", "n_o", "n_v", "n_lin", "k", "n_l"))
    nm2, nw2 = recip_dims(rc)
    assert np_ >= 0 and nm >= 0 and nm2 >= 1, "N'_m = N_p + N_m >= 1 (spec 3.1 on the compiled circuit)"
    assert nv >= 1 and k >= 0 and nlin >= nv - 1
    assert len(rc["w_n"]) == np_ == len(rc["a_n"])
    assert len(rc["w_m"]) == nm == len(rc["a_m"])
    assert len(rc["w_l"]) == nl == len(rc["a_l"])
    # Inputs: f_m w_V meets the first kN_v compiled multiplicative rows (numerators first).
    # f_l w_V: the spec (4.2) requires only N_l + N_r >= kN_v of the compiled circuit, but the
    # relation of 4.1 adds w_V to the rows of W_l only; we require N_l >= kN_v so that the two
    # agree (reported as an ambiguity).
    assert not rc["f_l"] or nl >= k * nv, "f_l = 1 needs N_l >= k N_v"
    assert not rc["f_m"] or nm2 >= k * nv, "f_m = 1 needs N_p + N_m >= k N_v"
    assert k == 0 or rc["f_l"] or rc["f_m"]
    assert len(rc["partition"]) == no and len(set(map(tuple, rc["partition"]))) == no
    for slot, t in rc["partition"]:
        assert slot in SLOTS and 0 <= t < (nm2 if slot == "nO" else nlin)
    init = recip_initial_cols(rc)
    recip_cols = set(range(nm2, nm2 + np_))
    for row in rc["w_n"]:
        for col, _ in row:
            assert col in init, f"W_n uses non-initial column {col}"
    for row in rc["w_m"] + rc["w_l"]:
        for col, _ in row:
            assert 0 <= col < nw2
    for row in rc["recip"]:
        for col, _, t in row["terms"]:
            if t is None:
                assert col in init or col in recip_cols, f"pole-free term on column {col}"
            else:
                assert col in init, f"pole term on non-initial column {col}"


def recip_wprime(rc, wit, w_P):
    """w' = w_D || w_L || w_P || w_R || w_O."""
    assert len(wit["w_D"]) == rc["n_p"] == len(w_P)
    assert len(wit["w_L"]) == rc["n_m"] == len(wit["w_R"]) and len(wit["w_O"]) == rc["n_o"]
    return wit["w_D"] + wit["w_L"] + w_P + wit["w_R"] + wit["w_O"]


def recip_wv(wit):
    return [x for v in wit["v"] for x in v]


def recip_numerators(rc, wit):
    """(W_n w' + f_m w_V + a_n)_i. W_n reads initial columns only, so w_P, w_R and the l_R
    elements are replaced by zeros here: the numerators are fixed before alpha."""
    nm2, _ = recip_dims(rc)
    init = recip_initial_cols(rc)
    w = recip_wprime(rc, wit, [0] * rc["n_p"])
    w = [x if i in init else 0 for i, x in enumerate(w)]
    wv = recip_wv(wit)
    return [(x + rc["f_m"] * (wv[i] if i < len(wv) else 0) + rc["a_n"][i]) % L
            for i, x in enumerate(sparse_mul(rc["w_n"], w))]


def recip_reciprocals(rc, wit, alpha):
    """Spec 4.3 step 3: w_P,i = num_i / (alpha + w_D,i); fails if alpha + w_D,i = 0."""
    out = []
    for d, num in zip(wit["w_D"], recip_numerators(rc, wit)):
        if (alpha + d) % L == 0:
            raise ReciprocalError("alpha + w_D,i = 0")
        out.append(num * inv(alpha + d) % L)
    return out


def recip_row_residual(rc, wit, row):
    """A reciprocal row as a rational function of X: ({pole value t: total multiplicity at
    1/(X + t)}, polynomial part), with w_P,i(X) = num_i / (X + w_D,i). The row vanishes iff
    every multiplicity and the polynomial part are zero (the 1/(X + t) for distinct t and 1 are
    linearly independent in F(X))."""
    nm2, _ = recip_dims(rc)
    num = recip_numerators(rc, wit)
    w = recip_wprime(rc, wit, [None] * rc["n_p"])
    mult, poly = {}, 0

    def add(t, x):
        mult[t % L] = (mult.get(t % L, 0) + x) % L

    for col, c, t in row["terms"]:
        if t is not None:
            add(t, c * w[col])
        elif nm2 <= col < nm2 + rc["n_p"]:
            i = col - nm2
            add(wit["w_D"][i], c * num[i])
        else:
            poly += c * w[col]
    for c, t in row["consts"]:
        if t is None:
            poly += c
        else:
            add(t, c)
    return {t: m for t, m in mult.items() if m}, poly % L


def recip_ordinary_residuals(rc, wit, w_P):
    """Residuals of the ordinary rows of 4.1 for a given w_P (= w_P(alpha)):
    (W_l w' + f_l w_V + a_l, W_m w' + f_m w~_V + a_m - w_L o w_R)."""
    w = recip_wprime(rc, wit, w_P)
    wv = recip_wv(wit)
    np_ = rc["n_p"]
    lin = [(x + rc["f_l"] * (wv[t] if t < len(wv) else 0) + rc["a_l"][t]) % L
           for t, x in enumerate(sparse_mul(rc["w_l"], w))]
    mul = [(x + rc["f_m"] * (wv[np_ + t] if np_ + t < len(wv) else 0) + rc["a_m"][t]
            - wit["w_L"][t] * wit["w_R"][t]) % L
           for t, x in enumerate(sparse_mul(rc["w_m"], w))]
    return lin, mul


def recip_satisfied(rc, wit, alpha):
    """Spec 4.1. The reciprocal rows must vanish as rational functions of X; the ordinary rows
    are checked with w_P = w_P(alpha) (they may read w_P, so they depend on alpha: the spec
    does not say at which X they hold; reported). Returns (recip_ok, ordinary_ok)."""
    recip_ok = all(recip_row_residual(rc, wit, row) == ({}, 0) for row in rc["recip"])
    lin, mul = recip_ordinary_residuals(rc, wit, recip_reciprocals(rc, wit, alpha))
    return recip_ok, not any(lin) and not any(mul)


def recip_compile(rc, alpha):
    """Spec 4.2: the section-3 circuit for a challenge alpha. Raises ReciprocalError if
    alpha + t = 0 for a public pole t (the spec does not cover this case; reported)."""
    recip_check_shape(rc)
    np_ = rc["n_p"]
    nm2, _ = recip_dims(rc)
    w_m = [list(row) + [(nm2 + i, -alpha % L)] for i, row in enumerate(rc["w_n"])]
    w_m += [list(row) for row in rc["w_m"]]
    w_l = [list(row) for row in rc["w_l"]]
    a_r = []
    for row in rc["recip"]:
        acc = {}
        for col, c, t in row["terms"]:
            if t is None:
                x = c
            else:
                if (alpha + t) % L == 0:
                    raise ReciprocalError("alpha + t = 0 for a public pole")
                x = c * inv(alpha + t)
            acc[col] = (acc.get(col, 0) + x) % L
        # one term per column, in the order of first appearance (any order gives the same
        # constraint; the order only matters for the section-3 digest, which is not used here)
        w_l.append([(col, x) for col, x in acc.items()])
        const = 0
        for c, t in row["consts"]:
            if t is None:
                const += c
            else:
                if (alpha + t) % L == 0:
                    raise ReciprocalError("alpha + t = 0 for a public pole")
                const += c * inv(alpha + t)
        a_r.append(const % L)
    c = {"n_m": nm2, "n_o": rc["n_o"], "n_v": rc["n_v"], "n_lin": rc["n_lin"], "k": rc["k"],
         "n_l": rc["n_l"] + len(rc["recip"]), "f_l": rc["f_l"], "f_m": rc["f_m"],
         "partition": [list(x) for x in rc["partition"]],
         "w_m": w_m, "a_m": [x % L for x in rc["a_n"] + rc["a_m"]],
         "w_l": w_l, "a_l": [x % L for x in rc["a_l"]] + a_r}
    circuit_check_shape(c)
    assert np_ + rc["n_m"] == len(c["w_m"])
    return c


def recip_compiled_witness(wit, w_P):
    """(w'_L, w'_R, w_O) and the inputs, as a section-3 witness."""
    return {"w_L": wit["w_D"] + wit["w_L"], "w_R": w_P + wit["w_R"], "w_O": list(wit["w_O"]),
            "v": wit["v"], "s": wit["s"]}


def recip_prove(rc, wit, rnd, chal, gammas):
    """Prover of spec 4.3 with given randomness and challenges (alpha in chal). Steps 1-3 are
    done explicitly (C_L, C_O from the initial witness alone, then w_P and C_R); step 4 runs the
    section-3 prover on the compiled circuit, whose own C_L, C_R, C_O must coincide."""
    recip_check_shape(rc)
    nm2, _ = recip_dims(rc)
    alpha = chal["alpha"]
    G, H, _ = circuit_gens({"n_lin": rc["n_lin"], "n_m": nm2})
    V = [circuit_input_commit(G, H, v, s) for v, s in zip(wit["v"], wit["s"])]
    # 1. the initial witness only: w_R, w_P and the l_R elements are unknown (zero) here
    shape = {"n_m": nm2, "n_lin": rc["n_lin"], "partition": rc["partition"]}
    pre = {"w_L": wit["w_D"] + wit["w_L"], "w_R": [0] * nm2,
           "w_O": [0 if slot == "lR" else x for x, (slot, _) in zip(wit["w_O"], rc["partition"])]}
    C_L, C_O = circuit_commit_initial(shape, pre, rnd)
    # 2.-3. alpha, reciprocals, C_R
    w_P = recip_reciprocals(rc, wit, alpha)
    cwit = recip_compiled_witness(wit, w_P)
    C_R = circuit_commit_right(shape, cwit, rnd)
    # 4. inner protocol on the compiled circuit
    c = recip_compile(rc, alpha)
    proof = circuit_prove(c, cwit, rnd, chal, gammas)
    assert proof["V"] == V and proof["C_L"] == C_L and proof["C_O"] == C_O and proof["C_R"] == C_R
    proof.update({"w_P": w_P, "compiled": c, "compiled_wit": cwit})
    return proof


def recip_verify(rc, V, C_L, C_R, C_O, C_S, chal, rounds, l_final, n_final, gammas, single=False):
    """Verifier of spec 4.3: compile for alpha, then the section-3 verifier (naive, or the
    single multiscalar equation)."""
    try:
        c = recip_compile(rc, chal["alpha"])
    except ReciprocalError:
        return False
    f = circuit_verify_msm if single else circuit_verify
    return f(c, V, C_L, C_R, C_O, C_S, chal, rounds, l_final, n_final, gammas)


def recip_self_check(rc, wit, chal, gammas, proof):
    """Self-checks of a reciprocal proof: the satisfaction check against the compiled circuit,
    the reciprocal rows at alpha, the section-3 checks (identity, opening, both verifiers) on
    the compiled circuit, and both reciprocal verifiers. Returns (satisfied, verifies)."""
    alpha = chal["alpha"]
    recip_ok, ord_ok = recip_satisfied(rc, wit, alpha)
    satisfied = recip_ok and ord_ok
    c, cwit, w_P = proof["compiled"], proof["compiled_wit"], proof["w_P"]
    # w_P is the reciprocal: (alpha + w_D,i) w_P,i = num_i
    num = recip_numerators(rc, wit)
    assert all((alpha + d) * p % L == x for d, p, x in zip(wit["w_D"], w_P, num))
    # the reciprocal rows evaluated at alpha = the compiled linear rows N_l.. on w'(alpha)
    w = recip_wprime(rc, wit, w_P)
    nl = rc["n_l"]
    at_alpha = [(x + c["a_l"][nl + q]) % L for q, x in enumerate(sparse_mul(c["w_l"][nl:], w))]
    for q, row in enumerate(rc["recip"]):
        mult, poly = recip_row_residual(rc, wit, row)
        direct = (poly + sum(m * inv(alpha + t) for t, m in mult.items())) % L
        assert direct == at_alpha[q], "compiled reciprocal row != rational function at alpha"
        if (mult, poly) == ({}, 0):
            assert at_alpha[q] == 0
        else:
            assert at_alpha[q] != 0, "a non-vanishing reciprocal row vanishes at alpha (unlucky alpha)"
    # compiled circuit satisfied by (w'_L, w'_R, w_O) iff the reciprocal circuit is (at alpha)
    _, csat = circuit_error(c, cwit, chal["lambda"], chal["rho"] * chal["rho"] % L)
    assert csat == satisfied
    s3, v3 = circuit_self_check(c, cwit, chal, gammas, proof)
    assert s3 == satisfied and v3 == satisfied
    args = (rc, proof["V"], proof["C_L"], proof["C_R"], proof["C_O"], proof["C_S"], chal,
            proof["rounds"], proof["l_final"], proof["n_final"], gammas)
    verifies = recip_verify(*args)
    assert recip_verify(*args, single=True) == verifies == v3
    return satisfied, verifies


# ---------------------------------------------------------------------------------------------
# Range proofs and multi-asset transactions (spec section 5, paper sections 6.4-6.5)
#
# Front ends that build reciprocal form circuits (section 4) column for column as the spec
# prescribes; they are proven with recip_prove and checked with recip_self_check.

U64 = 2**64


def range_layout(B, b):
    """Spec 5.1: the digit layout [(weight g_j, radix r_j)] of the range [0, B) in base b, in
    construction order (the paper's Cases 1-3, plus a radix-B digit for B < b)."""
    assert B >= 2 and b >= 2
    lay, S, p = [], 0, 1
    while S + (b - 1) * p <= B - 1:  # 1. powers of b while they fit
        lay.append((p, b))
        S += (b - 1) * p
        p *= b
    R = B - 1 - S
    if R == 0:
        return lay
    if R % (b - 1) == 0 and R // (b - 1) <= S + 1:  # 2. Case 1: one more base-b digit
        lay.append((R // (b - 1), b))
    elif R <= S + 1:  # 3. Case 2: a binary digit
        lay.append((R, 2))
    elif R >= b - 1:  # 4. Case 3: a base-b digit, then a binary digit for the rest
        g = R // (b - 1)
        lay.append((g, b))
        S += (b - 1) * g
        R -= (b - 1) * g
        if R > 0:
            assert R < b - 1 <= S + 1
            lay.append((R, 2))
    else:  # 5. B < b
        assert S == 0 and B < b and 2 <= R < b - 1
        lay.append((1, R + 1))
    return lay


def range_layout_order(layout):
    """Digit indices in increasing weight; ties: the later digit counts as larger (spec 5.1)."""
    return sorted(range(len(layout)), key=lambda j: (layout[j][0], j))


def range_decompose(x, layout, strict=True):
    """Spec 5.1: digits of x, from the largest weight down, d_j = max(0, ceil((x - M_j)/g_j)),
    M_j the maximum of the digits of smaller weight. strict=False accepts x >= B (for
    unsatisfied vectors): the excess then lands in the largest digit, which leaves its radix,
    and sum_j g_j d_j = x still holds."""
    assert x >= 0
    order = range_layout_order(layout)
    M, acc = {}, 0
    for j in order:
        M[j] = acc
        acc += (layout[j][1] - 1) * layout[j][0]
    d = [0] * len(layout)
    rem = x
    for j in reversed(order):
        g = layout[j][0]
        d[j] = max(0, -((M[j] - rem) // g))  # ceil((rem - M_j) / g)
        rem -= d[j] * g
        assert 0 <= rem <= M[j]
    assert rem == 0 and sum(g * dj for (g, _), dj in zip(layout, d)) == x
    if strict:
        assert all(0 <= dj < r for (_, r), dj in zip(layout, d)), "x outside [0, B)"
    return d


def range_tables(radices):
    """Spec 5.2 tables: the distinct radices in ascending order and the offset of each table's
    multiplicities m_{r,1..r-1} in the concatenation; returns (tables, offsets, N_O)."""
    tables = sorted(set(radices))
    off, n = {}, 0
    for r in tables:
        off[r] = n
        n += r - 1
    return tables, off, n


def range_multiplicities(digits, radices):
    """m_{r,s} (s = 1..r-1) per table, concatenated. Digits outside [1, r) are not counted
    (value 0 is implicit; a digit >= r, possible only in an unsatisfied witness, has no slot)."""
    tables, off, n = range_tables(radices)
    m = [0] * n
    for d, r in zip(digits, radices):
        if 1 <= d < r:
            m[off[r] + d - 1] += 1
    return m


def range_table_rows(radices, n_mp, mult_col):
    """Spec 5.2 reciprocal rows, one per table r: (w_P,p, 1) for the poles p of radix r in pole
    order; then per s = 1..r-1 the terms (m_{r,s}, 1, pole 0) and (m_{r,s}, -1, pole s); the
    constant (-N_r, pole 0). radices[p] is the radix of pole p (None for a non-digit pole),
    n_mp = N'_m (w_P,p is column N'_m + p), mult_col the column of the first multiplicity."""
    digit_radices = [r for r in radices if r is not None]
    tables, off, _ = range_tables(digit_radices)
    rows = []
    for r in tables:
        terms = [(n_mp + p, 1, None) for p, rp in enumerate(radices) if rp == r]
        for s in range(1, r):
            col = mult_col + off[r] + s - 1
            terms += [(col, 1, 0), (col, L - 1, s)]
        nr = sum(rp == r for rp in digit_radices)
        rows.append({"terms": terms, "consts": [(-nr % L, 0)]})
    return rows


def range_circuit(ranges, base):
    """Spec 5.2: the reciprocal form circuit for m ranges [A_i, B_i) in base b. Returns
    (rc, info) with info = {"layouts", "radices" (per pole), "inline"}."""
    assert 2 <= base <= 256 and len(ranges) >= 1
    for A, B in ranges:
        assert 0 <= A and A + 2 <= B <= U64
    layouts = [range_layout(B - A, base) for A, B in ranges]
    poles = [(i, g, r) for i, lay in enumerate(layouts) for g, r in lay]
    np_ = len(poles)
    radices = [r for _, _, r in poles]
    _, _, n_mult = range_tables(radices)
    inline = n_mult <= np_
    m = len(ranges)
    w_l = [[(p, -g % L) for p, (i2, g, _) in enumerate(poles) if i2 == i] for i in range(m)]
    rc = {"n_p": np_, "n_m": 0, "n_o": n_mult, "n_v": 1, "n_lin": 0 if inline else n_mult,
          "k": m, "n_l": m, "f_l": 1, "f_m": 0,
          "partition": [["nO" if inline else "lL", t] for t in range(n_mult)],
          "w_n": [[] for _ in range(np_)], "a_n": [1] * np_, "w_m": [], "a_m": [],
          "w_l": w_l, "a_l": [-A % L for A, _ in ranges],
          "recip": range_table_rows(radices, np_, 2 * np_)}
    recip_check_shape(rc)
    return rc, {"layouts": layouts, "radices": radices, "inline": inline}


def range_witness(values, blindings, ranges, base, strict=True):
    """Spec 5.2 witness: w_D = the digits of v_i - A_i (range after range), w_O = the
    multiplicities, inputs v_i with blindings s_i. strict=False: see range_decompose."""
    assert len(values) == len(blindings) == len(ranges)
    digits = []
    for v, (A, B) in zip(values, ranges):
        digits += range_decompose(v - A, range_layout(B - A, base), strict)
    radices = [r for A, B in ranges for _, r in range_layout(B - A, base)]
    return {"w_D": [d % L for d in digits], "w_L": [], "w_R": [],
            "w_O": range_multiplicities(digits, radices),
            "v": [[v % L] for v in values], "s": [s % L for s in blindings]}


def mact_circuit(n_in, n_out, base):
    """Spec 5.3: the reciprocal form circuit of a multi-asset transaction with n_in inputs and
    n_out outputs in base b. Returns (rc, info)."""
    k = n_in + n_out
    assert k >= 1 and 2 <= base <= 256
    lay = range_layout(U64, base)
    np_ = k + n_out * len(lay)
    radices = [None] * k + [r for _ in range(n_out) for _, r in lay]
    _, _, n_mult = range_tables([r for r in radices if r is not None])
    inline = n_mult <= np_
    n_lin = max(k, 0 if inline else n_mult)
    C = lambda i: 2 * np_ + i  # noqa: E731  amount copy c_i
    dpole = lambda j, x: k + j * len(lay) + x  # noqa: E731  digit x of output j
    w_n = [[(C(i), 1 if i < n_in else L - 1)] for i in range(k)] + [[] for _ in range(np_ - k)]
    a_n = [0] * k + [1] * (np_ - k)
    w_l = []
    for i in range(k):
        w_l.append([(C(i), L - 1)])  # a_i - c_i = 0
        w_l.append([(i, L - 1)])  # t_i - w_D,i = 0
    for j in range(n_out):
        w_l.append([(dpole(j, x), -g % L) for x, (g, _) in enumerate(lay)] + [(C(n_in + j), 1)])
    recip = [{"terms": [(np_ + i, 1, None) for i in range(k)], "consts": []}]
    recip += range_table_rows(radices, np_, C(k))
    rc = {"n_p": np_, "n_m": 0, "n_o": k + n_mult, "n_v": 2, "n_lin": n_lin, "k": k,
          "n_l": len(w_l), "f_l": 1, "f_m": 0,
          "partition": [["lO", i] for i in range(k)]
          + [["nO" if inline else "lL", t] for t in range(n_mult)],
          "w_n": w_n, "a_n": a_n, "w_m": [], "a_m": [], "w_l": w_l, "a_l": [0] * len(w_l),
          "recip": recip}
    recip_check_shape(rc)
    return rc, {"layout": lay, "radices": radices, "inline": inline}


def mact_witness(inputs, outputs, base, strict=True, digits=None):
    """Spec 5.3 witness from inputs/outputs [(amount, asset type, blinding)]. strict=False
    lets an output amount be >= 2^64 (range_decompose); digits overrides the digits of the
    outputs (a list per output, None to keep), for unsatisfied vectors; the linear rows must
    still hold."""
    entries = list(inputs) + list(outputs)
    lay = range_layout(U64, base)
    out_digits = []
    for j, (a, _, _) in enumerate(outputs):
        d = range_decompose(a, lay, strict)
        if digits is not None and digits[j] is not None:
            d = list(digits[j])
            assert len(d) == len(lay) and sum(g * x for (g, _), x in zip(lay, d)) == a
        out_digits += d
    radices = [r for _ in outputs for _, r in lay]
    return {"w_D": [t % L for _, t, _ in entries] + [d % L for d in out_digits],
            "w_L": [], "w_R": [],
            "w_O": [a % L for a, _, _ in entries] + range_multiplicities(out_digits, radices),
            "v": [[a % L, t % L] for a, t, _ in entries], "s": [s % L for _, _, s in entries]}


def range_layout_self_check():
    """Spec 5.1 checks: every layout is exact (the digit sums are exactly [0, B), with
    sum (r_j - 1) g_j = B - 1), satisfies the sorted-prefix rule, and every decomposition is
    valid; pure power layouts give the ordinary base-b digits."""

    def exact_small(B, b, lay):
        sums = {0}
        for g, r in lay:
            sums = {s + d * g for s in sums for d in range(r)}
        assert sums == set(range(B)), (B, b, lay)

    def prefix_rule(B, b, lay):
        acc = 0
        for j in range_layout_order(lay):
            g, r = lay[j]
            assert 1 <= g <= acc + 1 and 2 <= r <= max(b, 2), (B, b, lay)
            acc += (r - 1) * g
        assert acc == B - 1

    def paper_counts(B, b):
        """(digits, radices) of the paper's 6.4.1: Case 1 ((b-1) | (B-1)) and Case 2
        (b^(n-1) < B <= 2 b^(n-1)) n digits, Case 3 n + 1, n = ceil(log_b B); B < b: one
        digit of radix B (B = 2: radix 2)."""
        if B <= b:
            return 1, {B}
        n = 1
        while b**n < B:
            n += 1
        if (B - 1) % (b - 1) == 0:
            return n, {b}
        return (n, {b, 2}) if B <= 2 * b ** (n - 1) else (n + 1, {b, 2})

    def check_counts(B, b, lay):
        nd, rad = paper_counts(B, b)
        assert len(lay) == nd and {r for _, r in lay} == rad, (B, b, lay)

    for b in range(2, 257):
        for B in range(2, 300):
            lay = range_layout(B, b)
            prefix_rule(B, b, lay)
            check_counts(B, b, lay)
            exact_small(B, b, lay)
            assert all(r in (b, 2) for _, r in lay) or (B < b and lay == [(1, B)])
            if b in (2, 3, 4, 16, 256):
                for x in range(B):
                    range_decompose(x, lay)
    rng = random.Random(5)
    large = [U64, U64 - 1, U64 // 3, 2**63 + 1, 10**18, 16**15 + 1, 2 * 16**15 + 7,
             16**15 * 15, 256**7 * 3 + 5, 2**40 + 2**20, 1000, 4097]
    large += [rng.randrange(2, U64 + 1) for _ in range(20)]
    for b in (2, 3, 4, 7, 10, 16, 255, 256):
        for B in large:
            lay = range_layout(B, b)
            prefix_rule(B, b, lay)
            check_counts(B, b, lay)
            xs = [0, 1, B - 1, B // 2] + [rng.randrange(B) for _ in range(200)]
            for x in xs:
                d = range_decompose(x, lay)
                if B == b ** len(lay) and all(r == b for _, r in lay):
                    assert d == [(x // b**j) % b for j in range(len(lay))]
            # an out-of-range value: the decomposition still satisfies the linear row, and
            # some digit leaves its radix
            d = range_decompose(B + rng.randrange(B), lay, strict=False)
            assert any(not 0 <= x < r for (_, r), x in zip(lay, d))
    for b in (2, 3, 4, 16):  # counts for a longer stretch of small B
        for B in range(300, 5000):
            check_counts(B, b, range_layout(B, b))
    # B = 2^64 in base 16 / 256 / 2: the plain powers
    assert range_layout(U64, 16) == [(16**j, 16) for j in range(16)]
    assert range_layout(U64, 256) == [(256**j, 256) for j in range(8)]
    assert range_layout(U64, 2) == [(2**j, 2) for j in range(64)]


def range_circuit_self_check():
    """Semantic checks of the section-5 circuits without proving: the reciprocal circuit
    (spec 4.1, at a random alpha) is satisfied exactly when the statement holds. Range: every
    value in [A, B + 5) for small ranges, out-of-range values decomposed with strict=False.
    MACT: balanced / unbalanced amounts, digit tampering that keeps the linear row."""
    rng = random.Random(7)
    for b in (2, 3, 4, 16):
        for B in (2, 3, 5, 10, 16, 17, 31, 64, 100):
            A = rng.randrange(1000)
            rc, info = range_circuit([(A, A + B)], b)
            assert info["layouts"][0] == range_layout(B, b)
            for v in range(A, A + B + 5):
                wit = range_witness([v], [1], [(A, A + B)], b, strict=v < A + B)
                recip_ok, ord_ok = recip_satisfied(rc, wit, rng.randrange(1, L))
                assert ord_ok and recip_ok == (v < A + B), (b, B, v)
                # wrong multiplicities break the table rows
                wit["w_O"][0] += 1
                assert not recip_satisfied(rc, wit, rng.randrange(1, L))[0]
    ranges = [(0, U64), (5, 1005), (3, 5)]
    for b in (2, 4, 16):
        rc, _ = range_circuit(ranges, b)
        for vals, ok in (([0, 5, 3], True), ([U64 - 1, 1004, 4], True), ([7, 1005, 3], False),
                         ([U64, 5, 4], False), ([1, 6, 5], False)):
            wit = range_witness(vals, [1, 2, 3], ranges, b, strict=ok)
            assert recip_satisfied(rc, wit, rng.randrange(1, L)) == (ok, True)
    t0, t1 = rng.randrange(L), rng.randrange(L)
    for b in (4, 16):
        rc, _ = mact_circuit(2, 2, b)
        lay = range_layout(U64, b)
        for ins, outs, ok in ((([9, t0, 1], [U64 - 1, t1, 2]), ([U64 - 1, t1, 3], [9, t0, 4]), True),
                              (([9, t0, 1], [7, t1, 2]), ([8, t0, 3], [8, t1, 4]), False),
                              (([9, t0, 1], [7, t0, 2]), ([8, t0, 3], [8, t0, 4]), True),
                              (([9, t0, 1], [7, t0, 2]), ([8, t0, 3], [8, t1, 4]), False)):
            wit = mact_witness(ins, outs, b)
            assert recip_satisfied(rc, wit, rng.randrange(1, L)) == (ok, True)
        d = range_decompose(b + 3, lay)
        d[0] += b
        d[1] -= 1
        wit = mact_witness([(b + 3, t0, 1), (0, t1, 2)], [(b + 3, t0, 3), (0, t1, 4)], b,
                           digits=[d, None])
        assert recip_satisfied(rc, wit, rng.randrange(1, L)) == (False, True)

#!/usr/bin/env python3
"""Writes tests/vectors/bppp/*.json from the reference (python3 ref/gen_vectors.py).
Deterministic: the same output on every run."""

import json
import os
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bppp_ref import (L, SLOTS, U64, ReciprocalError, Sym, circuit_prove,  # noqa: E402
                      circuit_self_check, inv, mact_circuit, mact_witness, range_circuit,
                      range_circuit_self_check, range_decompose, range_layout, range_layout_self_check,
                      range_witness,
                      recip_compile, recip_numerators, recip_prove, recip_self_check,
                      wnla_commit, wnla_prove, wnla_rounds, wnla_verify)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "vectors", "bppp")


def hx(x):
    """A scalar as 32 little-endian bytes in hex (curve25519-dalek Scalar::to_bytes)."""
    return (x % L).to_bytes(32, "little").hex()


def wnla_case(rng, a, b):
    G = Sym.gen("G")
    H = [Sym.gen("H", i) for i in range(a)]
    N = [Sym.gen("N", i) for i in range(b)]
    s = lambda: rng.randrange(1, L)  # noqa: E731
    c, l, n = [s() for _ in range(a)], [s() for _ in range(a)], [s() for _ in range(b)]
    rho = s()
    k, _, _ = wnla_rounds(a, b)
    gammas = [s() for _ in range(k)]
    C = wnla_commit(G, H, N, c, rho * rho % L, l, n)
    gi = iter(gammas)
    rounds, lf, nf = wnla_prove(G, H, N, c, rho, list(l), list(n), lambda X, R: next(gi))
    assert wnla_verify(G, H, N, c, rho, C, rounds, lf, nf, gammas)
    bad = [(lf[0] + 1) % L] + lf[1:] if lf else lf
    assert not lf or not wnla_verify(G, H, N, c, rho, C, rounds, bad, nf, gammas)

    def pt(p):
        g, h, nn = p.coeffs(a, b)
        return {"g": hx(g), "h": [hx(x) for x in h], "n": [hx(x) for x in nn]}

    return {
        "a": a, "b": b,
        "rho": hx(rho), "c": [hx(x) for x in c], "l": [hx(x) for x in l], "n": [hx(x) for x in n],
        "gammas": [hx(x) for x in gammas],
        "rounds": [{"X": pt(X), "R": pt(R)} for X, R in rounds],
        "l_final": [hx(x) for x in lf], "n_final": [hx(x) for x in nf],
    }


def sparse_rows(rng, nrows, ncols):
    """Random sparse rows: each entry non-zero with probability 1/2, columns ascending."""
    return [[[col, rng.randrange(1, L)] for col in range(ncols) if rng.random() < 0.5]
            for _ in range(nrows)]


def make_partition(rng, kind, no, nm, nlin):
    """"none" (N_O = 0), "nO" (all of w_O in n_O) or "spread" (over n_O, l_O, l_L, l_R, each
    used at least once), in random order."""
    if kind == "none":
        assert no == 0
        return []
    avail = {X: [(X, t) for t in range(nm if X == "nO" else nlin)] for X in SLOTS}
    if kind == "nO":
        slots = rng.sample(avail["nO"], no)
    else:
        assert kind == "spread" and no >= 4
        first = [rng.choice(avail[X]) for X in SLOTS]
        rest = [x for X in SLOTS for x in avail[X] if x not in first]
        slots = first + rng.sample(rest, no - 4)
        rng.shuffle(slots)
    return [[X, t] for X, t in slots]


def circuit_case(rng, name, nm, no, nv, nlin, k, nl, fl, fm, part, violate=None):
    """A random circuit that the random witness satisfies (a_l, a_m solved for), optionally
    broken afterwards: ("lin", t) shifts a_l[t], ("mul", t) shifts a_m[t], ("input", i, j)
    shifts v_{i,j} after the circuit is fixed."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    nw = 2 * nm + no
    c = {"n_m": nm, "n_o": no, "n_v": nv, "n_lin": nlin, "k": k, "n_l": nl, "f_l": fl, "f_m": fm,
         "partition": make_partition(rng, part, no, nm, nlin),
         "w_l": sparse_rows(rng, nl, nw), "w_m": sparse_rows(rng, nm, nw)}
    wit = {"w_L": [s() for _ in range(nm)], "w_R": [s() for _ in range(nm)],
           "w_O": [s() for _ in range(no)], "v": [[s() for _ in range(nv)] for _ in range(k)],
           "s": [s() for _ in range(k)]}
    w = wit["w_L"] + wit["w_R"] + wit["w_O"]
    wv = [x for v in wit["v"] for x in v]
    pad = lambda f, t: f * wv[t] if t < len(wv) else 0  # noqa: E731
    c["a_l"] = [-(sum(x * w[col] for col, x in row) + pad(fl, t)) % L
                for t, row in enumerate(c["w_l"])]
    c["a_m"] = [(wit["w_L"][t] * wit["w_R"][t] - sum(x * w[col] for col, x in row) - pad(fm, t)) % L
                for t, row in enumerate(c["w_m"])]
    if violate is not None:
        if violate[0] == "lin":
            c["a_l"][violate[1]] = (c["a_l"][violate[1]] + s()) % L
        elif violate[0] == "mul":
            c["a_m"][violate[1]] = (c["a_m"][violate[1]] + s()) % L
        else:
            assert violate[0] == "input" and (fl or fm)
            _, i, j = violate
            wit["v"][i][j] = (wit["v"][i][j] + s()) % L
    rnd = {"r_O": [s() for _ in range(6)], "r_L": [s() for _ in range(5)],
           "r_R": [s() for _ in range(4)], "l_S": [s() for _ in range(nlin)],
           "n_S": [s() for _ in range(nm)]}
    chal = {x: s() for x in ("rho", "lambda", "beta", "delta", "tau")}
    gammas = [s() for _ in range(wnla_rounds(7 + nlin, nm)[0])]
    proof = circuit_prove(c, wit, rnd, chal, gammas)
    satisfied, verifies = circuit_self_check(c, wit, chal, gammas, proof)
    assert satisfied == (violate is None)

    def pt(p):
        g, h, nn = p.coeffs(7 + nlin, nm)
        return {"g": hx(g), "h": [hx(x) for x in h], "n": [hx(x) for x in nn]}

    hxs = lambda v: [hx(x) for x in v]  # noqa: E731
    rows = lambda m: [[[col, hx(x)] for col, x in row] for row in m]  # noqa: E731
    return {
        "name": name,
        "n_m": nm, "n_o": no, "n_v": nv, "n_lin": nlin, "k": k, "n_l": nl, "f_l": fl, "f_m": fm,
        "partition": c["partition"],
        "w_l": rows(c["w_l"]), "a_l": hxs(c["a_l"]), "w_m": rows(c["w_m"]), "a_m": hxs(c["a_m"]),
        "w_L": hxs(wit["w_L"]), "w_R": hxs(wit["w_R"]), "w_O": hxs(wit["w_O"]),
        "v": [hxs(v) for v in wit["v"]], "s": hxs(wit["s"]),
        "rand": {x: hxs(rnd[x]) for x in ("r_O", "r_L", "r_R", "l_S", "n_S")},
        "chal": {x: hx(chal[x]) for x in ("rho", "lambda", "beta", "delta", "tau")},
        "gammas": hxs(gammas),
        "satisfied": satisfied,
        "V": [pt(x) for x in proof["V"]],
        "C_L": pt(proof["C_L"]), "C_R": pt(proof["C_R"]), "C_O": pt(proof["C_O"]),
        "C_S": pt(proof["C_S"]),
        "wnla_c": hxs(proof["wnla_c"]), "wnla_l": hxs(proof["wnla_l"]),
        "wnla_n": hxs(proof["wnla_n"]),
        "rounds": [{"X": pt(X), "R": pt(R)} for X, R in proof["rounds"]],
        "l_final": hxs(proof["l_final"]), "n_final": hxs(proof["n_final"]),
        "verifies": verifies,
    }


# (name, N_m, N_O, N_v, N_lin, k, N_l, f_l, f_m, partition[, violation])
CIRCUITS = [
    # all four (f_l, f_m), each with k in {1, 3} and N_v in {1, 4}
    # Without flags the inputs enter no constraint, so k = 0 (spec 3.1).
    ("f00-k0-v1-min", 1, 0, 1, 0, 0, 1, 0, 0, "none"),
    ("f00-k0-v4", 3, 3, 4, 3, 0, 2, 0, 0, "nO"),
    ("f00-k0-v1-spread", 4, 5, 1, 2, 0, 3, 0, 0, "spread"),
    ("f00-k0-v4-spread", 5, 6, 4, 5, 0, 4, 0, 0, "spread"),
    ("f10-k1-v1", 2, 2, 1, 0, 1, 2, 1, 0, "nO"),
    ("f10-k1-v4", 3, 6, 4, 5, 1, 5, 1, 0, "spread"),
    ("f10-k3-v1", 6, 0, 1, 1, 3, 4, 1, 0, "none"),
    ("f10-k3-v4", 4, 5, 4, 3, 3, 13, 1, 0, "spread"),
    ("f01-k1-v1-nl0", 1, 1, 1, 0, 1, 0, 0, 1, "nO"),
    ("f01-k1-v4", 4, 4, 4, 4, 1, 3, 0, 1, "spread"),
    ("f01-k3-v1", 3, 2, 1, 2, 3, 2, 0, 1, "nO"),
    ("f01-k3-v4", 12, 6, 4, 3, 3, 5, 0, 1, "spread"),
    ("f11-k1-v1", 2, 4, 1, 1, 1, 3, 1, 1, "spread"),
    ("f11-k1-v4", 4, 4, 4, 3, 1, 4, 1, 1, "nO"),
    ("f11-k3-v1", 3, 3, 1, 0, 3, 3, 1, 1, "nO"),
    ("f11-k3-v4", 16, 8, 4, 6, 3, 14, 1, 1, "spread"),
    # sizes and layouts
    ("odd-sizes", 7, 9, 2, 5, 2, 6, 1, 1, "spread"),
    ("nO-full", 8, 8, 1, 2, 0, 5, 0, 0, "nO"),
    ("lin-heavy", 2, 10, 3, 8, 2, 7, 1, 0, "spread"),
    ("nm13-no0", 13, 0, 2, 1, 2, 4, 0, 1, "none"),
    ("nm16-no0-v1", 16, 0, 1, 0, 1, 3, 1, 1, "none"),
    ("k0", 3, 4, 1, 1, 0, 3, 0, 0, "spread"),
    # unsatisfied
    ("bad-linear", 4, 5, 2, 3, 2, 4, 1, 0, "spread", ("lin", 3)),
    ("bad-mult", 5, 4, 1, 2, 1, 3, 0, 1, "spread", ("mul", 2)),
    ("bad-input-v0", 4, 4, 2, 2, 2, 4, 1, 0, "spread", ("input", 1, 0)),
    ("bad-input-cross", 8, 4, 4, 3, 2, 8, 1, 1, "spread", ("input", 1, 2)),
]


# ---------------------------------------------------------------------------------------------
# Reciprocal form (spec section 4)


def recip_run(rng, name, rc, wit, expect):
    """Randomness and challenges, prove, self-check, and the vector entry."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    nm2 = rc["n_p"] + rc["n_m"]
    rnd = {"r_O": [s() for _ in range(6)], "r_L": [s() for _ in range(5)],
           "r_R": [s() for _ in range(4)], "l_S": [s() for _ in range(rc["n_lin"])],
           "n_S": [s() for _ in range(nm2)]}
    chal = wit.pop("chal")
    gammas = [s() for _ in range(wnla_rounds(7 + rc["n_lin"], nm2)[0])]
    proof = recip_prove(rc, wit, rnd, chal, gammas)
    satisfied, verifies = recip_self_check(rc, wit, chal, gammas, proof)
    assert satisfied == verifies == expect, (name, satisfied, verifies)

    def pt(p):
        g, h, nn = p.coeffs(7 + rc["n_lin"], nm2)
        return {"g": hx(g), "h": [hx(x) for x in h], "n": [hx(x) for x in nn]}

    hxs = lambda v: [hx(x) for x in v]  # noqa: E731
    rows = lambda m: [[[col, hx(x)] for col, x in row] for row in m]  # noqa: E731
    opt = lambda t: None if t is None else hx(t)  # noqa: E731
    return {
        "name": name,
        **{x: rc[x] for x in ("n_p", "n_m", "n_o", "n_v", "n_lin", "k", "n_l", "f_l", "f_m")},
        "partition": [list(x) for x in rc["partition"]],
        "w_n": rows(rc["w_n"]), "a_n": hxs(rc["a_n"]),
        "w_m": rows(rc["w_m"]), "a_m": hxs(rc["a_m"]),
        "w_l": rows(rc["w_l"]), "a_l": hxs(rc["a_l"]),
        "recip": [{"terms": [[col, hx(c), opt(t)] for col, c, t in row["terms"]],
                   "consts": [[hx(c), opt(t)] for c, t in row["consts"]]} for row in rc["recip"]],
        "w_D": hxs(wit["w_D"]), "w_L": hxs(wit["w_L"]), "w_R": hxs(wit["w_R"]),
        "w_O": hxs(wit["w_O"]), "v": [hxs(v) for v in wit["v"]], "s": hxs(wit["s"]),
        "rand": {x: hxs(rnd[x]) for x in ("r_O", "r_L", "r_R", "l_S", "n_S")},
        "chal": {x: hx(chal[x]) for x in ("alpha", "rho", "lambda", "beta", "delta", "tau")},
        "gammas": hxs(gammas),
        "satisfied": satisfied,
        "w_P": hxs(proof["w_P"]),
        "V": [pt(x) for x in proof["V"]],
        "C_L": pt(proof["C_L"]), "C_R": pt(proof["C_R"]), "C_O": pt(proof["C_O"]),
        "C_S": pt(proof["C_S"]),
        "rounds": [{"X": pt(X), "R": pt(R)} for X, R in proof["rounds"]],
        "l_final": hxs(proof["l_final"]), "n_final": hxs(proof["n_final"]),
        "verifies": verifies,
    }


def challenges(rng):
    return {x: rng.randrange(1, L) for x in ("alpha", "rho", "lambda", "beta", "delta", "tau")}


def range_case(rng, name, b, n, layout, v, digits=None, mult_delta=None):
    """Reciprocal range proof (paper 6.4): v = sum_j b^j d_j with the digits as private poles
    (numerator 1: W_n = 0, a_n = 1) and one reciprocal row
    sum_j w_P,j - sum_{s<b} m_s/(X + s) = 0, the multiplicities m in w_O: "inline" in n_O
    (needs b <= n), "shared" in l_L (N_lin = b). digits overrides the decomposition (then
    m counts the digits < b, the best multiplicities); mult_delta = (s, x) adds x to m_s."""
    if digits is None:
        digits = [(v // b**j) % b for j in range(n)]
        assert v < b**n
    assert len(digits) == n and sum(d * b**j for j, d in enumerate(digits)) == v
    m = [sum(d == s for d in digits) for s in range(b)]
    if mult_delta is not None:
        m[mult_delta[0]] += mult_delta[1]
    assert layout in ("inline", "shared") and (layout == "shared" or b <= n)
    slot = "nO" if layout == "inline" else "lL"
    rc = {"n_p": n, "n_m": 0, "n_o": b, "n_v": 1, "n_lin": 0 if layout == "inline" else b,
          "k": 1, "n_l": 1, "f_l": 1, "f_m": 0, "partition": [[slot, s] for s in range(b)],
          "w_n": [[] for _ in range(n)], "a_n": [1] * n, "w_m": [], "a_m": [],
          "w_l": [[(j, -b**j % L) for j in range(n)]], "a_l": [0],
          "recip": [{"terms": [(n + j, 1, None) for j in range(n)]
                     + [(2 * n + s, L - 1, s) for s in range(b)], "consts": []}]}
    wit = {"w_D": digits, "w_L": [], "w_R": [], "w_O": m, "v": [[v]], "s": [rng.randrange(1, L)],
           "chal": challenges(rng)}
    return rc, wit


def mact_case(rng, name, txs, b, n):
    """Multi-asset balance (paper 6.5) with range proofs of every amount, shared multiplicities.
    txs = [(amount, type index, o)] (o = 1 for outputs); two random asset types. N_v = 2,
    v_i = (amount_i, type_i), w_V = (a_0, t_0, a_1, t_1, ...). With f_m = 1, w_V meets the
    numerator rows in order, so pole 2i is the amount reciprocal a_i/(X + t_i) (w_D,2i = t_i,
    numerator w_V,2i = a_i), and pole 2i+1, whose numerator row receives t_i, is digit 0 of a_i
    with W_n row -w_D,2i and a_n = 1 (numerator -t_i + t_i + 1 = 1). Digits j >= 1 are poles
    2k + i(n-1) + j - 1 with numerator 1. With f_l = 1, linear row 2i is
    a_i - sum_j b^j d_ij = 0 and row 2i+1 the copy t_i - w_D,2i = 0. Reciprocal rows: the balance
    sum_i (-1)^o_i w_P,2i = 0 and the range row over all digit poles."""
    k = len(txs)
    types = [rng.randrange(1, L) for _ in range(2)]
    np_ = k * (n + 1)

    def dpole(i, j):
        return 2 * i + 1 if j == 0 else 2 * k + i * (n - 1) + j - 1

    w_D = [0] * np_
    w_n = [[] for _ in range(np_)]
    a_n = [1] * np_
    w_l, digits_all = [], []
    for i, (a, ti, _) in enumerate(txs):
        assert 0 <= a < b**n
        w_D[2 * i] = types[ti]
        a_n[2 * i] = 0
        w_n[2 * i + 1] = [(2 * i, L - 1)]
        for j in range(n):
            w_D[dpole(i, j)] = (a // b**j) % b
            digits_all.append((a // b**j) % b)
        w_l.append([(dpole(i, j), -b**j % L) for j in range(n)])
        w_l.append([(2 * i, L - 1)])
    m = [sum(d == s for d in digits_all) for s in range(b)]
    P = lambda i: np_ + i  # noqa: E731
    O = lambda s: 2 * np_ + s  # noqa: E731
    balance = {"terms": [(P(2 * i), L - 1 if o else 1, None) for i, (_, _, o) in enumerate(txs)],
               "consts": []}
    rng_row = {"terms": [(P(dpole(i, j)), 1, None) for i in range(k) for j in range(n)]
               + [(O(s), L - 1, s) for s in range(b)], "consts": []}
    rc = {"n_p": np_, "n_m": 0, "n_o": b, "n_v": 2, "n_lin": b, "k": k, "n_l": 2 * k,
          "f_l": 1, "f_m": 1, "partition": [["lL", s] for s in range(b)],
          "w_n": w_n, "a_n": a_n, "w_m": [], "a_m": [], "w_l": w_l, "a_l": [0] * (2 * k),
          "recip": [balance, rng_row]}
    wit = {"w_D": w_D, "w_L": [], "w_R": [], "w_O": m,
           "v": [[a, types[ti]] for a, ti, _ in txs], "s": [rng.randrange(1, L) for _ in txs],
           "chal": challenges(rng)}
    return rc, wit


def generic_case(rng, name, fl, fm, violate=False):
    """A mixed reciprocal form circuit: N_p = 3 private poles (w_D,0 = w_D,1 a private value p,
    w_D,2 a public pole t*), N_m = 3 ordinary multiplications, k = 2 inputs with N_v = 2 (with
    f_m = 1 they meet the three numerators and the first W_m row), w_O over all four slots.
    Reciprocal rows: reciprocals (one column repeated), public poles with multiplicities in w_L,
    w_D and w_O, constants with and without poles, pole-free terms on initial columns. Ordinary
    rows read w_P; w_R is solved from the multiplications and the two l_R elements from the two
    linear rows that read w_P and w_R, i.e. the prover computes them after alpha, and the
    circuit itself does not depend on alpha. violate: shift a_n,0 afterwards (the reciprocal
    rows then fail; the ordinary rows still hold)."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    np_, nm, no, nv, nlin, k = 3, 3, 7, 2, 3, 2
    nl = 5 if fl else 3
    nm2 = np_ + nm
    D = lambda i: i  # noqa: E731
    Lc = lambda t: np_ + t  # noqa: E731
    P = lambda i: nm2 + i  # noqa: E731
    R = lambda t: nm2 + np_ + t  # noqa: E731
    O = lambda i: 2 * nm2 + i  # noqa: E731
    # w_O roles: 0 n_O (multiplicity of a public pole), 1 l_O (pole-free term), 2 l_L (copy of
    # w_D,0, multiplicity), 3 l_R (pivot), 4 n_O, 5 l_R (pivot), 6 l_O
    kinds = ["nO", "lO", "lL", "lR", "nO", "lR", "lO"]
    avail = {X: rng.sample(range(nm2 if X == "nO" else nlin), kinds.count(X)) for X in SLOTS}
    partition = [[X, avail[X].pop()] for X in kinds]
    init = list(range(nm2)) + [O(i) for i in (0, 1, 2, 4, 6)]
    p, tstar, t2, t4, t5 = s(), s(), s(), s(), s()
    w_D = [p, p, tstar]
    w_L = [s() for _ in range(nm)]
    w_O = [None, s(), p, None, s(), None, s()]
    v = [[s() for _ in range(nv)] for _ in range(k)]
    wv = [x for vi in v for x in vi]
    c0a, c0b, c1, c2, c3, c4, c5, c6, c7, e1, e2, e3, c9 = (s() for _ in range(13))
    c0 = (c0a + c0b) % L
    j, j2 = rng.randrange(nm), rng.randrange(nm)
    w_O[0] = -c5 * inv(c4) % L
    c8 = -(c6 * w_O[1] + c7 * w_L[j2]) % L
    recip = [
        {"terms": [(P(0), c0a, None), (P(1), c1, None), (Lc(j), c2, tstar), (O(0), c4, t2),
                   (O(1), c6, None), (P(2), c3, None), (P(0), c0b, None), (Lc(j2), c7, None)],
         "consts": [(c5, t2), (c8, None)]},
        {"terms": [(O(2), 1, t4), (P(2), e1, None), (D(0), L - 1, t4), (P(0), e2, None),
                   (P(1), e2 * c1 * inv(c0) % L, None), (Lc(j), e1 * c2 * inv(c3) % L, tstar),
                   (D(1), e3, None), (D(0), -e3 % L, None)],
         "consts": [(c9, t5), (-c9 % L, t5)]},
    ]
    w_n = [[(col, s()) for col in sorted(rng.sample(init, 2))] for _ in range(np_)]
    rc = {"n_p": np_, "n_m": nm, "n_o": no, "n_v": nv, "n_lin": nlin, "k": k, "n_l": nl,
          "f_l": fl, "f_m": fm, "partition": partition, "w_n": w_n, "a_n": [s(), 0, 0],
          "recip": recip}
    # solve a_n,1 and a_n,2: c0 num_0 + c1 num_1 = 0 (pole p), c2 w_L,j + c3 num_2 = 0 (pole t*)
    wit = {"w_D": w_D, "w_L": w_L, "w_R": [0] * nm, "w_O": [x or 0 for x in w_O], "v": v,
           "s": [s() for _ in range(k)]}
    num = recip_numerators(rc, wit)
    rc["a_n"][1] = (-c0 * num[0] * inv(c1) - num[1]) % L
    rc["a_n"][2] = (-c2 * w_L[j] * inv(c3) - num[2]) % L
    if violate:
        rc["a_n"][0] = (rc["a_n"][0] + s()) % L
    num = recip_numerators(rc, wit)
    chal = challenges(rng)
    w_P = [x * inv(chal["alpha"] + d) % L for x, d in zip(num, w_D)]
    # ordinary multiplications: W_m reads initial columns, w_P and earlier w_R; solve w_R,t
    w_m, a_m, w_R = [], [], [0] * nm
    for t in range(nm):
        cols = rng.sample(init, 2) + [P(rng.randrange(np_))] + ([R(t - 1)] if t else [])
        row = [(col, s()) for col in cols]
        w_m.append(row)
        a_m.append(s())
        w = w_D + w_L + w_P + w_R + wit["w_O"]
        rhs = (sum(x * w[col] for col, x in row) + fm * (wv[np_ + t] if np_ + t < len(wv) else 0)
               + a_m[t]) % L
        w_R[t] = rhs * inv(w_L[t]) % L
    # ordinary linear rows: rows 1 and nl - 1 read w_P, w_R and an l_R pivot (solved),
    # the others initial columns only (a_l solved)
    w_l, a_l = [], []
    for r in range(nl):
        row = [(col, s()) for col in rng.sample(init, 2)]
        pivot = {1: 3, nl - 1: 5}.get(r)
        if pivot is not None:
            row += [(P(rng.randrange(np_)), s()), (R(rng.randrange(nm)), s()), (O(pivot), s())]
        rng.shuffle(row)
        w = w_D + w_L + w_P + w_R + wit["w_O"]
        rest = (sum(x * w[col] for col, x in row) + fl * (wv[r] if r < len(wv) else 0)) % L
        if pivot is None:
            a_l.append(-rest % L)
        else:
            a_l.append(s())
            cp = dict((col, x) for col, x in row)[O(pivot)]
            wit["w_O"][pivot] = -(rest + a_l[r]) * inv(cp) % L
        w_l.append(row)
    rc.update({"w_m": w_m, "a_m": a_m, "w_l": w_l, "a_l": a_l})
    wit["w_R"] = w_R
    wit["chal"] = chal
    return rc, wit


def recip_edge_checks(rng):
    """alpha = -w_D,i makes the prover fail; alpha = -t for a public pole t makes the circuit
    uncompilable (the verifier rejects). Not vectors: such challenges have negligible
    probability and cannot be produced through the transcript."""
    rc, wit = range_case(rng, "edge", 4, 4, "shared", 27)
    wit.pop("chal")
    rnd = {"r_O": [1] * 6, "r_L": [1] * 5, "r_R": [1] * 4, "l_S": [1] * 4, "n_S": [1] * 4}
    chal = {x: 5 for x in ("rho", "lambda", "beta", "delta", "tau")}
    chal["alpha"] = -wit["w_D"][1] % L  # digit 2, also the public pole 2
    try:
        recip_prove(rc, wit, rnd, chal, [1] * wnla_rounds(11, 4)[0])
        raise AssertionError("prover accepted alpha = -w_D,i")
    except ReciprocalError:
        pass
    try:
        recip_compile(rc, chal["alpha"])
        raise AssertionError("compiled with alpha = -t")
    except ReciprocalError:
        pass


def reciprocal_cases(rng):
    cases = []
    # range proofs: bases 2, 4, 16; inline (n_O) and shared (l_L); values incl. 0 and b^n - 1
    for b, n in ((2, 8), (4, 8), (16, 16)):
        top = b**n - 1
        for layout, vals in (("inline", (0, rng.randrange(top))), ("shared", (top, rng.randrange(top)))):
            for v in vals:
                name = f"range-b{b}-n{n}-{layout}-v{'max' if v == top else v}"
                cases.append(recip_run(rng, name, *range_case(rng, name, b, n, layout, v), True))
    # multi-asset balance with range proofs of the amounts (base 4, 3 digits)
    txs = [(40, 0, 0), (25, 1, 0), (10, 0, 0), (50, 0, 1), (25, 1, 1)]
    cases.append(recip_run(rng, "mact-balanced", *mact_case(rng, "mact-balanced", txs, 4, 3), True))
    # generic mixed circuits
    for fl, fm in ((1, 1), (1, 0), (0, 1)):
        name = f"generic-f{fl}{fm}"
        cases.append(recip_run(rng, name, *generic_case(rng, name, fl, fm), True))
    # unsatisfied
    name = "bad-range-digit-eq-base"  # v = 4^4 with digits (4, 3, 3, 3), best multiplicities
    cases.append(recip_run(rng, name, *range_case(rng, name, 4, 4, "inline", 256, digits=[4, 3, 3, 3]),
                           False))
    name = "bad-range-wrong-multiplicity"
    cases.append(recip_run(rng, name, *range_case(rng, name, 2, 8, "shared", 77, mult_delta=(0, 1)),
                           False))
    txs = [(40, 0, 0), (25, 1, 0), (10, 0, 0), (51, 0, 1), (25, 1, 1)]
    cases.append(recip_run(rng, "bad-mact-unbalanced",
                           *mact_case(rng, "bad-mact-unbalanced", txs, 4, 3), False))
    name = "bad-generic-numerator"
    cases.append(recip_run(rng, name, *generic_case(rng, name, 1, 1, violate=True), False))
    return cases


# ---------------------------------------------------------------------------------------------
# Range proofs and multi-asset transactions (spec section 5)


def layout_json(lay):
    return [[str(g), r] for g, r in lay]


def range_vec(rng, name, base, ranges, values, violation=None):
    """A section-5.2 range proof. violation (a description) marks a value outside its range,
    decomposed with range_decompose(strict=False) so that the linear row holds and the top
    digit leaves its radix; such a case is unsatisfied, and its digits are not an honest
    decomposition ("digits_tampered": an implementation's witness builder refuses it, so the
    Rust side takes w_D, w_O from the vector)."""
    rc, info = range_circuit(ranges, base)
    blindings = [rng.randrange(1, L) for _ in values]
    in_range = all(A <= v < B for v, (A, B) in zip(values, ranges))
    assert in_range == (violation is None)
    wit = range_witness(values, blindings, ranges, base, strict=in_range)
    wit["chal"] = challenges(rng)
    entry = recip_run(rng, name, rc, wit, in_range)
    return {"name": name, "base": base, "ranges": [[str(A), str(B)] for A, B in ranges],
            "values": [str(v) for v in values], "blindings": [hx(x) for x in blindings],
            "violation": violation, "digits_tampered": not in_range,
            "layouts": [layout_json(x) for x in info["layouts"]],
            "multiplicities": "inline" if info["inline"] else "shared", **entry}


def mact_vec(rng, name, base, inputs, outputs, violation=None, digits=None):
    """A section-5.3 transaction; inputs/outputs = [(amount, asset index)], with random asset
    types and blindings. Satisfied iff balanced per asset, outputs in [0, 2^64) and the digits
    honest. An output >= 2^64 is decomposed with strict=False; digits overrides the digits of
    the outputs (both: "digits_tampered")."""
    assets = [rng.randrange(1, L) for _ in range(3)]
    ent = lambda xs: [(a, assets[t], rng.randrange(1, L)) for a, t in xs]  # noqa: E731
    ins, outs = ent(inputs), ent(outputs)
    rc, info = mact_circuit(len(ins), len(outs), base)
    in_range = all(a < U64 for a, _ in outputs)
    wit = mact_witness(ins, outs, base, strict=in_range, digits=digits)
    balanced = all(sum(a for a, t in inputs if t == x) == sum(a for a, t in outputs if t == x)
                   for x in range(3))
    expect = balanced and in_range and digits is None
    assert expect == (violation is None)
    wit["chal"] = challenges(rng)
    entry = recip_run(rng, name, rc, wit, expect)
    js = lambda xs: [{"amount": str(a), "asset": hx(t), "blinding": hx(s)}  # noqa: E731
                     for a, t, s in xs]
    return {"name": name, "base": base, "n_in": len(ins), "n_out": len(outs),
            "inputs": js(ins), "outputs": js(outs), "violation": violation,
            "digits_tampered": not in_range or digits is not None,
            "layout": layout_json(info["layout"]),
            "multiplicities": "inline" if info["inline"] else "shared", **entry}


def range_cases(rng):
    u = lambda B: rng.randrange(B)  # noqa: E731
    A = 1000
    cases = [
        # one 64-bit value, base 16: 16 digits, 15 multiplicities inline in n_O
        range_vec(rng, "u64-b16-v0", 16, [(0, U64)], [0]),
        range_vec(rng, "u64-b16-vmax", 16, [(0, U64)], [U64 - 1]),
        range_vec(rng, "u64-b16-rand", 16, [(0, U64)], [u(U64)]),
        # base 2: 64 binary digits, one multiplicity, inline (N_O = 1 <= N_p = 64)
        range_vec(rng, "u64-b2-rand", 2, [(0, U64)], [u(U64)]),
        # base 256: 8 digits, 255 multiplicities, shared (N_O > N_p)
        range_vec(rng, "u64-b256-rand", 256, [(0, U64)], [u(U64)]),
        # base 4: 32 digits, inline
        range_vec(rng, "u64-b4-max", 4, [(0, U64)], [U64 - 1]),
        # arbitrary ranges [1000, 1000 + B) in base 16, each layout kind
        range_vec(rng, "b16-powers-B4096", 16, [(A, A + 16**3)], [A + 16**3 - 1]),  # powers only
        range_vec(rng, "b16-extra-B556", 16, [(A, A + 556)], [A + u(556)]),  # + base-16 digit
        range_vec(rng, "b16-extra-bin-B1000", 16, [(A, A + 1000)], [A + 999]),  # + both
        range_vec(rng, "b16-bin-B4097", 16, [(A, A + 4097)], [A + 4096]),  # + binary digit
        range_vec(rng, "b16-small-B10", 16, [(A, A + 10)], [A + 7]),  # B < b: one radix-10 digit
        range_vec(rng, "b16-small-B2", 16, [(A, A + 2)], [A]),  # one binary digit
        # arbitrary ranges in small bases (inline multiplicities, ties in weight)
        range_vec(rng, "b4-extra-B1000", 4, [(A, A + 1000)], [A + u(1000)]),
        range_vec(rng, "b3-B100-case2", 3, [(7, 107)], [7 + 10]),  # powers + binary 19
        range_vec(rng, "b2-B1000", 2, [(A, A + 1000)], [A + u(1000)]),
        range_vec(rng, "b2-B3-tie", 2, [(5, 8)], [6]),  # x = 1: digits (1, 0) (the later digit is the larger)
        # ties in weight where the tie rule changes the digits: Case 1 digit 3 = power 3
        # (x = 4: digits (1, 1, 0)), Case 2 binary digit 16 = power 16 (x = 20: (4, 1, 0))
        range_vec(rng, "b3-B15-case1-tie", 3, [(0, 15)], [4]),
        range_vec(rng, "b16-B272-case2-tie", 16, [(A, A + 272)], [A + 20]),
        # an offset range ending at 2^64 (B - A = 2^64 - 12345)
        range_vec(rng, "offset-to-2^64-b16", 16, [(12345, U64)], [U64 - 1]),
        # aggregated, m = 3, different ranges
        range_vec(rng, "agg3-b16-shared", 16, [(0, U64), (A, A + 1000), (5, 15)],
                  [u(U64), A + u(1000), 14]),
        range_vec(rng, "agg3-b16-inline", 16, [(0, U64), (0, 2**32), (A, A + 4097)],
                  [u(U64), u(2**32), A + 4096]),
        range_vec(rng, "agg3-b4-mixed", 4, [(0, U64), (A, A + 1000), (3, 5)],
                  [u(U64), A, 4]),
        # unsatisfied: a value outside its range (top digit out of its radix)
        range_vec(rng, "bad-b16-B4097-v-eq-B", 16, [(A, A + 4097)], [A + 4097],
                  violation="value = B (outside [A, B)): digits (1, 0, 16, 0), digit 2 has value 16 "
                         "outside radix 16"),
        range_vec(rng, "bad-u64-b16-v-2^64", 16, [(0, U64)], [U64],
                  violation="value = 2^64: digit 15 has value 16 outside radix 16"),
        range_vec(rng, "bad-agg3-b16-second", 16, [(0, U64), (A, A + 1000), (5, 15)],
                  [u(U64), A + 1000 + 37, 5],
                  violation="value 2 = B + 37: its weight-49 digit leaves radix 16"),
        range_vec(rng, "bad-b16-small-B10", 16, [(A, A + 10)], [A + 10],
                  violation="value = B: the radix-10 digit has value 10"),
    ]
    return cases


def mact_cases(rng):
    u = lambda B: rng.randrange(B)  # noqa: E731
    x, y = u(2**62), u(2**62)
    a1, a2 = u(2**62), u(2**62)
    lay16 = range_layout(U64, 16)
    amt = 0x123456789abcdef0
    d = range_decompose(amt, lay16)
    assert d[1] >= 1
    tampered = list(d)
    tampered[0] += 16  # digit 0 out of radix 16, the linear row still holds
    tampered[1] -= 1
    cases = [
        mact_vec(rng, "b16-2in-2out-2assets", 16, [(x, 0), (y, 1)], [(y, 1), (x, 0)]),
        mact_vec(rng, "b16-3in-2out-2assets", 16, [(a1, 0), (y, 1), (a2, 0)],
                 [(a1 + a2, 0), (y, 1)]),
        mact_vec(rng, "b16-2in-2out-1asset", 16, [(a1, 0), (a2, 0)], [(a1 + a2 - 777, 0), (777, 0)]),
        mact_vec(rng, "b16-1in-3out", 16, [(U64 - 1, 0)], [(U64 - 1 - x - y, 0), (x, 0), (y, 0)]),
        mact_vec(rng, "b4-2in-2out-2assets", 4, [(x, 0), (y, 1)], [(x, 0), (y, 1)]),
        mact_vec(rng, "b4-2in-3out-3assets", 4, [(x + 5, 0), (y, 1)], [(5, 0), (y, 1), (x, 0)]),
        mact_vec(rng, "b2-1in-1out", 2, [(x, 2)], [(x, 2)]),
        mact_vec(rng, "b256-1in-1out-shared", 256, [(x, 0)], [(x, 0)]),
        mact_vec(rng, "b16-2in-0out-zero", 16, [(0, 0), (0, 1)], []),
        mact_vec(rng, "b16-0in-1out-zero", 16, [], [(0, 0)]),
        # unsatisfied
        mact_vec(rng, "bad-b16-unbalanced", 16, [(x, 0), (y, 1)], [(x + 1, 0), (y, 1)],
                 violation="output 0 exceeds input 0 (same asset) by one unit"),
        mact_vec(rng, "bad-b4-unbalanced-asset", 4, [(x, 0), (y, 1)], [(x, 1), (y, 0)],
                 violation="amounts swapped between the two assets"),
        mact_vec(rng, "bad-b16-digit-out-of-range", 16, [(amt, 0), (5, 1)], [(amt, 0), (5, 1)],
                 violation="output 0: digit 0 + 16, digit 1 - 1 (digit 0 outside radix 16, "
                           "the linear row holds)", digits=[tampered, None]),
        mact_vec(rng, "bad-b16-output-2^64", 16, [(2**63 + 3, 0), (2**63 + 2, 0)], [(U64 + 5, 0)],
                 violation="output amount 2^64 + 5 (inputs balance it): digit 15 has value 16"),
    ]
    return cases


def main():
    rng = random.Random(20261019)
    # (|l|, |n|): odd and unequal lengths, a frozen norm vector (|n| = 1, 2, 3 with long l),
    # stops on ties (3x3, 5x1) and an empty l.
    sizes = [(0, 0), (1, 1), (2, 3), (3, 3), (5, 1), (6, 1), (0, 8), (7, 1), (1, 7), (8, 8), (9, 13),
             (16, 64), (15, 33), (16, 1), (64, 2), (33, 3)]
    os.makedirs(OUT, exist_ok=True)
    cases = [wnla_case(rng, a, b) for a, b in sizes]
    with open(os.path.join(OUT, "wnla.json"), "w") as f:
        json.dump({"cases": cases}, f, indent=1)
        f.write("\n")
    print(f"wnla.json: {len(cases)} cases")

    rng = random.Random(20261020)
    cases = [circuit_case(rng, *args) for args in CIRCUITS]
    with open(os.path.join(OUT, "circuit.json"), "w") as f:
        json.dump({"cases": cases}, f, indent=1)
        f.write("\n")
    print(f"circuit.json: {len(cases)} cases")

    rng = random.Random(20261021)
    recip_edge_checks(rng)
    cases = reciprocal_cases(rng)
    with open(os.path.join(OUT, "reciprocal.json"), "w") as f:
        json.dump({"cases": cases}, f, indent=1)
        f.write("\n")
    print(f"reciprocal.json: {len(cases)} cases")

    range_layout_self_check()
    range_circuit_self_check()
    for fname, seed, gen in (("range.json", 20261022, range_cases), ("mact.json", 20261023, mact_cases)):
        cases = gen(random.Random(seed))
        with open(os.path.join(OUT, fname), "w") as f:
            json.dump({"cases": cases}, f, indent=1)
            f.write("\n")
        print(f"{fname}: {len(cases)} cases")


if __name__ == "__main__":
    main()

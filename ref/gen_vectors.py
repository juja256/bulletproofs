#!/usr/bin/env python3
"""Writes tests/vectors/bppp/*.json from the reference (python3 ref/gen_vectors.py).
Deterministic: the same output on every run."""

import json
import os
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bppp_ref import (L, ONE, SLOTS, U64, Builder, BuilderError,  # noqa: E402
                      BuilderProverError, ReciprocalError, Sym, bld_agreement_check, bld_apply,
                      bld_costs, bld_finalize, bld_lower, bld_parse_lc, bld_run_program,
                      bld_self_check, bld_semantic, circuit_prove,
                      circuit_self_check, inv, mact_circuit, mact_witness, range_circuit,
                      range_circuit_self_check, range_decompose, range_layout, range_layout_self_check,
                      range_witness,
                      recip_compile, recip_numerators, recip_prove, recip_satisfied,
                      recip_self_check, wnla_commit, wnla_prove, wnla_rounds, wnla_verify)

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


# ---------------------------------------------------------------------------------------------
# The circuit builder (spec section 7)


def lc(*terms):
    """A JSON LC: each term is a variable (coefficient 1), (variable, coefficient) or an int
    (a One term with that coefficient)."""
    out = []
    for t in terms:
        if isinstance(t, int):
            out.append([["1"], hx(t)])
        elif isinstance(t[0], str):
            out.append([list(t), hx(1)])
        else:
            out.append([list(t[0]), hx(t[1])])
    return out


class Prog:
    """Writes a program (JSON operations) while applying it to a live Builder, so that the
    prover's values can be read back to build satisfied programs."""

    def __init__(self):
        self.ops, self.b, self.failed = [], Builder(), None

    def _op(self, op):
        assert self.failed is None, "an error case ends with its failing operation"
        self.ops.append(op)
        return bld_apply(self.b, op)

    def fail(self, method, *args):
        """Apply an operation that must fail (the last of the program)."""
        try:
            getattr(self, method)(*args)
        except BuilderError:
            self.failed = len(self.ops) - 1
            return
        raise AssertionError(f"{method}{args} did not fail")

    def val(self, jlc):
        return self.b.eval(bld_parse_lc(jlc))

    def commit(self, v, s):
        return self._op({"op": "commit", "v": hx(v), "s": hx(s)})

    def multiply(self, l, r):
        return self._op({"op": "multiply", "l": l, "r": r})

    def allocate(self, v):
        return self._op({"op": "allocate", "v": hx(v)})

    def allocate_multiplier(self, a, b):
        return self._op({"op": "allocate_multiplier", "l": hx(a), "r": hx(b)})

    def constrain(self, x):
        return self._op({"op": "constrain", "lc": x})

    def witness(self, v):
        return self._op({"op": "witness", "v": hx(v)})

    def product(self, l, r, out):
        return self._op({"op": "product", "l": l, "r": r, "out": out})

    def table(self, widths, rows):
        return self._op({"op": "table", "widths": widths, "rows": rows})

    def lookup(self, t, tup):
        return self._op({"op": "lookup", "table": t, "tuple": tup})

    def lookup_value(self, t, v):
        return self._op({"op": "lookup_value", "table": t, "v": v})

    def reciprocal(self, widths, terms, public=()):
        return self._op({"op": "reciprocal", "widths": widths,
                         "terms": [{"num": n, "tuple": t} for n, t in terms],
                         "public": [{"coeff": c, "row": r} for c, r in public]})


def builder_case(rng, name, P, expect=True):
    """Replay the program from its JSON, finalize, lower (7.6), check, prove (recip_run)."""
    ops = json.loads(json.dumps(P.ops))
    b, err = bld_run_program(ops)
    assert err == P.failed, (name, err, P.failed)
    base = {"name": name, "program": ops, "error": err, "prover_error": False}
    if err is not None:
        assert err == len(ops) - 1
        return base
    fin_v = bld_finalize(b, prover=False)
    rc_v, _ = bld_lower(b, fin_v)  # the verifier's lowering needs no values
    try:
        fin = bld_finalize(b)
    except BuilderProverError:
        assert expect == "prover_error", name
        base["prover_error"] = True
        return base
    assert expect != "prover_error", name
    rc, wit = bld_lower(b, fin)
    assert rc == rc_v
    costs = bld_costs(b, fin)
    assert costs["bppp_gates"] == rc["n_p"] + rc["n_m"]
    sem = bld_semantic(b, fin)
    assert sem == expect, (name, sem)
    recip_ok, ord_ok = recip_satisfied(rc, wit, rng.randrange(1, L))
    assert (recip_ok and ord_ok) == sem, (name, recip_ok, ord_ok)
    bld_agreement_check(b, random.Random(name))
    wit["chal"] = challenges(rng)
    entry = recip_run(rng, name, rc, wit, expect)
    del entry["name"]
    return {**base, "costs": costs, **entry}


def builder_cases(rng):
    s = lambda: rng.randrange(1, L)  # noqa: E731
    cases = []

    def add(name, P, expect=True):
        cases.append(builder_case(rng, name, P, expect))

    def range_table(P, w):
        return P.table([w], [[i] for i in range(2**w)])

    # -- satisfied programs
    # builder mode without any gate: n = n_prod = N_p = 0, so n_r = 1 (one zero multiplier)
    P = Prog()
    x1, x2 = s(), s()
    a, b = P.witness(x1), P.witness(x2)
    P.constrain(lc(a, b, -(x1 + x2) % L))
    add("no-gates-witness-constraint", P)

    P = Prog()
    v = s()
    V0 = P.commit(v, s())
    w = P.witness(v)
    P.constrain(lc(V0, (w, L - 1)))
    add("no-gates-committed-input", P)

    # R1CS operations mixed with builder operations; pending allocate; committed inputs in
    # tuples and numerators; MultiplierRight in numerators (copies)
    P = Prog()
    V0, V1 = P.commit(5, s()), P.commit(s(), s())
    L0, R0, O0 = P.multiply(lc(V0, 2), lc(V1))
    xv, yv = s(), s()
    L1 = P.allocate(xv)
    L2, R2, O2 = P.multiply(lc((O0, 3)), lc(V0, (V1, 2)))  # leaves multiplier 1 pending
    R1 = P.allocate(yv)                                     # fills multiplier 1
    L3 = P.allocate(9)                                      # multiplier 3 stays pending
    pl, pr = s(), s()
    L4, R4, O4 = P.allocate_multiplier(pl, pr)
    P.constrain(lc(O4, (L4, -pr % L)))
    P.constrain(lc(("O", 1), (R1, -xv % L)))
    P.constrain(lc(L3, -9 % L))
    P.constrain(lc(("O", 3)))
    P.constrain(lc(("R", 3), 0))
    wv = 7 * P.val(lc(V1)) % L
    W0 = P.witness(wv)
    P.constrain(lc(W0, (V1, L - 7)))
    W1 = P.witness(P.val(lc(V1)))
    W2 = P.witness(xv)
    W3 = P.witness(9 * yv % L)
    P.product(lc(L3), lc(R1, (L1, 2)), lc(W3, (L1, 2 * 9 % L), (R1, 0)))
    P.reciprocal([8], [(lc(V0), [lc(W1)]), (lc((V0, L - 1)), [lc(V1)]),
                       (lc(R1, 4), [lc(L1)]), (lc((R1, L - 1), (ONE, L - 4)), [lc(W2)])])
    add("r1cs-mixed-pending-copies", P)

    # a single allocate (pending: a_R = a_O = 0) used by a product
    P = Prog()
    Lp = P.allocate(7)
    W0 = P.witness(21)
    P.product(lc(Lp), lc(("R", 0), 3), lc(W0))
    add("allocate-once-pending", P)

    # products with constants in l, r, out, and out reading other variables
    P = Prog()
    V0 = P.commit(s(), s())
    av, bv = s(), s()
    A, B = P.witness(av), P.witness(bv)
    C = P.witness(((av + 5) * (2 * bv + 1) - 3 * av - 11) % L)
    P.product(lc(A, 5), lc((B, 2), 1), lc(C, (A, 3), 11))
    P.product(lc(7), lc(B), lc((B, 7)))
    Sq = P.witness(P.val(lc(V0)) ** 2 % L)
    P.product(lc(V0), lc(V0), lc(Sq))
    P.product(lc(A, (B, 2), (A, L - 1)), lc(3), lc((B, 6), (A, 3), (A, L - 3)))
    add("products-constants", P)

    # range check through a one-column 4-bit table; lookup of a committed input and of an LC
    # that is not exactly one term; no gates at all besides the lookups (N_m = 0)
    P = Prog()
    V0 = P.commit(11, s())
    t = range_table(P, 4)
    P.lookup_value(t, 13)
    y = P.witness(7)
    P.lookup(t, [lc(y)])
    P.lookup(t, [lc(y, 2)])
    P.lookup(t, [lc(V0)])
    P.lookup(t, [lc(5)])
    P.lookup_value(t, 0)
    P.lookup_value(t, 15)
    add("range-4bit-lookups", P)

    # duplicate rows (the first equal row counts), a table never looked up (no
    # multiplicities), an unused table between used ones
    P = Prog()
    t0 = P.table([2, 2], [[0, 1], [1, 2]])
    t1 = P.table([3], [[1], [2], [2], [5], [7]])
    t2 = P.table([5], [[31], [0]])
    t3 = range_table(P, 2)
    P.lookup_value(t1, 2)
    P.lookup_value(t3, 3)
    P.lookup_value(t1, 2)
    P.lookup_value(t1, 5)
    y = P.witness(7)
    P.lookup(t1, [lc(y)])
    assert (t0, t2) == (0, 2)
    add("tables-duplicate-and-unused", P)

    # multi-column tables: XOR on 2-bit values, a split table [4, 2, 2]; components with
    # merged coefficients, a constant, an unbounded variable merged to zero, a + 4b
    P = Prog()
    tr = range_table(P, 2)
    A = P.lookup_value(tr, 2)
    B = P.lookup_value(tr, 3)
    C = P.witness(1)
    P.lookup(tr, [lc(C)])
    tx = P.table([2, 2, 2], [[i, j, i ^ j] for i in range(4) for j in range(4)])
    P.lookup(tx, [lc(A), lc(B), lc(C)])
    P.lookup(tx, [lc((A, 2), (A, L - 1)), lc(B), lc(C)])
    P.lookup(tx, [lc(1), lc(B), lc(A)])
    U = P.witness(s())
    P.lookup(tx, [lc(A, U, (U, L - 1)), lc(B), lc(C)])
    ts = P.table([4, 2, 2], [[n, n & 3, n >> 2] for n in range(16)])
    P.lookup(ts, [lc(A, (B, 4)), lc(A), lc(B)])  # bound 3 + 4*3 = 15 = 2^4 - 1
    P.lookup(ts, [lc((A, 4), 1), lc(1), lc(A)])
    add("xor-and-split-tables", P)

    # memory-style permutation, 2 components: writes added, reads subtracted, public terms
    # with a constant coefficient, with MultiplierRight + constant (copy), with
    # MultiplierLeft; a numerator with MultiplierRight (copy); a component MultiplierRight
    P = Prog()
    tr = range_table(P, 4)
    Lm, Rm, Om = P.allocate_multiplier(5, 3)
    P.lookup(tr, [lc(Rm)])
    P.lookup(tr, [lc(Lm)])
    a0, v0 = P.lookup_value(tr, 1), P.lookup_value(tr, 9)
    a1, v1 = P.lookup_value(tr, 2), P.lookup_value(tr, 4)
    P.reciprocal([4, 4],
                 [(lc(1), [lc(a0), lc(v0)]), (lc(Rm), [lc(a1), lc(v1)]),
                  (lc(L - 1), [lc(a1), lc(v1)]), (lc((Lm, L - 1)), [lc(Rm), lc(v1)])],
                 [(lc(L - 1), [1, 9]), (lc((Rm, L - 1), 1), [2, 4]), (lc(Lm), [3, 4])])
    add("memory-permutation-2col", P)

    # MACT-style balance: amounts (committed) as numerators, asset types as unbounded poles
    # (one committed, one a witness)
    P = Prog()
    t0, t1 = s(), s()
    In0, In1 = P.commit(100, s()), P.commit(50, s())
    Out0, Out1, Out2 = P.commit(70, s()), P.commit(30, s()), P.commit(50, s())
    T0 = P.commit(t0, s())
    T1 = P.witness(t1)
    P.reciprocal([252], [(lc(In0), [lc(T0)]), (lc(In1), [lc(T1)]), (lc((Out0, L - 1)), [lc(T0)]),
                         (lc((Out1, L - 1)), [lc(T0)]), (lc((Out2, L - 1)), [lc(T1)])])
    add("mact-balance-weighted", P)

    # many witnesses: w_O overflows n_O into l_O (N_lin > 0)
    P = Prog()
    V0 = P.commit(s(), s())
    tr = range_table(P, 2)
    ws = [P.witness(s()) for _ in range(10)]
    P.lookup_value(tr, 1)
    P.lookup_value(tr, 3)
    pv = P.val(lc(ws[0])) * P.val(lc(ws[1])) % L
    Wp = P.witness(pv)
    P.product(lc(ws[0]), lc(ws[1]), lc(Wp))
    P.constrain(lc(*ws, V0, -sum(P.val(lc(x)) for x in ws + [V0]) % L))
    add("witnesses-overflow-into-lO", P)

    # an argument without terms is dropped; an argument with public terms only (a constant
    # coefficient, a witness sum, a zero-constant coefficient, an empty coefficient)
    P = Prog()
    av = s()
    A, B = P.witness(av), P.witness(-(av + 2) % L)
    P.reciprocal([3], [])
    P.reciprocal([3, 5], [], [(lc(2), [1, 2]), (lc(A, B), [1, 2]), (lc(0), [7, 31]),
                              (lc(), [0, 0])])
    add("empty-and-public-only-arguments", P)

    # the widest valid list (sum 252), a coefficient 2^64 - 1, row entries 2^64 - 1
    P = Prog()
    tr = range_table(P, 2)
    A = P.lookup_value(tr, 1)
    B = P.lookup_value(tr, 3)
    t252 = P.table([252], [[U64 - 1], [0]])
    P.lookup_value(t252, U64 - 1)
    P.reciprocal([126, 126], [(lc(1), [lc((A, U64 - 1)), lc(B)]), (lc(1), [lc(B), lc(A)])],
                 [(lc(L - 1), [U64 - 1, 3]), (lc(L - 1), [3, 1])])
    add("width-sum-252-coeff-2^64-1", P)

    # -- unsatisfied
    P = Prog()
    av, bv = s(), s()
    A, B, C = P.witness(av), P.witness(bv), P.witness(av * bv + 1)
    P.product(lc(A), lc(B), lc(C))
    add("bad-product", P, False)

    P = Prog()
    A, B = P.witness(s()), P.witness(s())
    P.reciprocal([64], [(lc(1), [lc(A)]), (lc(L - 1), [lc(B)])])
    add("bad-reciprocal-not-vanishing", P, False)

    P = Prog()
    tr = range_table(P, 2)
    A, B = P.lookup_value(tr, 1), P.lookup_value(tr, 2)
    P.reciprocal([2, 2], [(lc(1), [lc(A), lc(B)]), (lc(L - 1), [lc(B), lc(A)])],
                 [(lc(1), [1, 2]), (lc(L - 1), [2, 1])])
    add("bad-reciprocal-public-swapped", P, False)

    # -- prover errors (a lookup equal to no row)
    P = Prog()
    t = range_table(P, 3)
    P.lookup_value(t, 9)
    add("prover-error-lookup-value", P, "prover_error")

    P = Prog()
    tr = range_table(P, 2)
    A, B, C = P.lookup_value(tr, 1), P.lookup_value(tr, 2), P.lookup_value(tr, 0)
    tx = P.table([2, 2, 2], [[i, j, i ^ j] for i in range(4) for j in range(4)])
    P.lookup(tx, [lc(A), lc(B), lc(C)])
    add("prover-error-xor-tuple", P, "prover_error")

    # -- construction errors (the failing operation is the last)
    def err(name, build):
        P = Prog()
        build(P)
        assert P.failed is not None
        add(name, P)

    def xor_setup(P):
        tr = range_table(P, 2)
        A, B = P.lookup_value(tr, 1), P.lookup_value(tr, 2)
        tx = P.table([2, 2, 2], [[i, j, i ^ j] for i in range(4) for j in range(4)])
        return tr, A, B, tx

    def e_unbounded(P):
        tr, A, B, tx = xor_setup(P)
        U = P.witness(3)
        P.fail("lookup", tx, [lc(A), lc(B), lc(U)])
    err("err-unbounded-component", e_unbounded)

    def e_bound_2w(P):
        tr, A, B, tx = xor_setup(P)
        t22 = P.table([2, 2], [[i, j] for i in range(4) for j in range(4)])
        P.lookup(t22, [lc(A), lc(B)])           # bound 3 = 2^2 - 1: accepted
        P.fail("lookup", t22, [lc(A, 1), lc(B)])  # bound 4 = 2^2: rejected
    err("err-bound-exactly-2^w", e_bound_2w)

    def e_bound_2w_sum(P):
        tr, A, B, tx = xor_setup(P)
        ts = P.table([4, 2, 2], [[n, n & 3, n >> 2] for n in range(16)])
        P.lookup(ts, [lc(A, (B, 4)), lc(A), lc(B)])        # 15: accepted
        P.fail("lookup", ts, [lc(A, (B, 4), 1), lc(A), lc(B)])  # 16: rejected
    err("err-bound-sum-exactly-2^w", e_bound_2w_sum)

    def e_coeff(P):
        tr, A, B, tx = xor_setup(P)
        P.reciprocal([126, 126], [(lc(1), [lc((A, U64 - 1)), lc(B)])],
                     [(lc(L - 1), [U64 - 1, 2])])
        P.fail("reciprocal", [126, 126], [(lc(1), [lc((A, U64)), lc(B)])])
    err("err-coefficient-2^64", e_coeff)

    def e_const(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("reciprocal", [126, 126], [(lc(1), [lc(A, U64), lc(B)])])
    err("err-constant-2^64", e_const)

    def e_neg(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("lookup", tx, [lc((A, L - 1), 3), lc(B), lc(1)])
    err("err-negative-coefficient", e_neg)

    def e_merged_neg(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("lookup", tx, [lc(A, (A, L - 2), 2), lc(B), lc(A)])  # merged -1
    err("err-merged-negative-coefficient", e_merged_neg)

    def e_not_recorded(P):
        tr = range_table(P, 2)
        X = P.witness(1)
        P.lookup(tr, [lc((X, 2))])  # not exactly (x, 1): no bound
        P.lookup(tr, [lc(X, 0)])    # two terms: no bound
        tx = P.table([2, 2, 2], [[i, j, i ^ j] for i in range(4) for j in range(4)])
        P.fail("lookup", tx, [lc(X), lc(X), lc(0)])
    err("err-bound-only-from-exact-term", e_not_recorded)

    def e_after(P):
        tr = range_table(P, 2)
        X = P.witness(1)
        tx = P.table([2, 2, 2], [[i, j, i ^ j] for i in range(4) for j in range(4)])
        P.fail("lookup", tx, [lc(X), lc(X), lc(0)])  # X's range lookup would come later
    err("err-bound-not-yet-recorded", e_after)

    def e_recip_no_bound(P):
        X = P.witness(1)
        P.reciprocal([2], [(lc(1), [lc(X)])], [(lc(L - 1), [1])])  # records no bound
        P.fail("reciprocal", [2, 2], [(lc(1), [lc(X), lc(X)])])
    err("err-bound-not-from-reciprocal", e_recip_no_bound)

    err("err-width-sum-253-table", lambda P: P.fail("table", [126, 127], [[0, 0]]))

    def e_253_recip(P):
        P.reciprocal([126, 126], [])
        P.fail("reciprocal", [200, 53], [])
    err("err-width-sum-253-empty-reciprocal", e_253_recip)
    err("err-width-0", lambda P: P.fail("table", [4, 0], [[1, 0]]))
    err("err-table-entry-ge-2^w", lambda P: P.fail("table", [3], [[0], [7], [8]]))
    err("err-empty-table", lambda P: P.fail("table", [3], []))

    def e_row_len(P):
        P.fail("table", [3, 3], [[1, 2], [3]])
    err("err-table-row-length", e_row_len)

    def e_lv_2col(P):
        t = P.table([2, 2], [[1, 1]])
        P.fail("lookup_value", t, 1)
    err("err-lookup-value-two-columns", e_lv_2col)

    def e_tuple_len(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("lookup", tx, [lc(A), lc(B)])
    err("err-tuple-length", e_tuple_len)

    def e_unknown(P):
        tr = range_table(P, 2)
        X = P.witness(1)
        P.fail("lookup", 5, [lc(X)])
    err("err-unknown-table", e_unknown)

    def e_var(P):
        A, B = P.witness(1), P.witness(2)
        P.fail("product", lc(A), lc(B), lc(("W", 5)))
    err("err-variable-does-not-exist", e_var)

    def e_var_recip(P):
        V0 = P.commit(1, 2)
        X = P.witness(1)
        P.fail("reciprocal", [3], [(lc(V0, ("V", 1)), [lc(X)])])
    err("err-variable-does-not-exist-numerator", e_var_recip)

    def e_pub_len(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("reciprocal", [3, 3], [(lc(1), [lc(A), lc(B)])], [(lc(L - 1), [1])])
    err("err-public-row-length", e_pub_len)

    def e_pub_entry(P):
        X = P.witness(1)
        P.fail("reciprocal", [3], [(lc(1), [lc(X)])], [(lc(L - 1), [8])])
    err("err-public-row-entry-ge-2^w", e_pub_entry)
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

    bld_self_check()
    cases = builder_cases(random.Random(20261024))
    with open(os.path.join(OUT, "builder.json"), "w") as f:
        json.dump({"cases": cases}, f, indent=1)
        f.write("\n")
    print(f"builder.json: {len(cases)} cases")


if __name__ == "__main__":
    main()

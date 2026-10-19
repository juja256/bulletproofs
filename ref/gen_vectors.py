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
                      bld_self_check, bld_semantic, bld_uses_eta, circuit_prove,
                      circuit_self_check, inv, mact_circuit, mact_witness, pole_poly,
                      range_circuit, range_circuit_self_check, range_decompose, range_layout,
                      range_layout_self_check, range_witness, recip_compile, recip_digest,
                      recip_eta_witness, recip_numerators, recip_prove, recip_satisfied,
                      recip_self_check, recip_tuples, recip_uses_eta, recip_v2_self_check, wnla_commit, wnla_prove, wnla_rounds, wnla_verify)

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


def recip_run(rng, name, rc, wit, expect, extra=False):
    """Randomness and challenges, prove, self-check, and the vector entry. extra: also
    "uses_eta" and "digest" (spec 4.4), and for a circuit that uses eta (protocol v2) "tuples",
    "chal"."eta", "w_D_eta" and every public pole as a list (its pole polynomial); without
    extra (range.json, mact.json) the entry is the v1 entry of phase 5."""
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
    v2 = recip_uses_eta(rc)
    assert extra or not v2

    def opt(t):
        if t is None:
            return None
        p = pole_poly(t)
        if v2:
            return hxs(p)
        assert len(p) == 1
        return hx(p[0])

    head = {
        "name": name,
        **{x: rc[x] for x in ("n_p", "n_m", "n_o", "n_v", "n_lin", "k", "n_l", "f_l", "f_m")},
        "partition": [list(x) for x in rc["partition"]],
        "w_n": rows(rc["w_n"]), "a_n": hxs(rc["a_n"]),
        "w_m": rows(rc["w_m"]), "a_m": hxs(rc["a_m"]),
        "w_l": rows(rc["w_l"]), "a_l": hxs(rc["a_l"]),
        "recip": [{"terms": [[col, hx(c), opt(t)] for col, c, t in row["terms"]],
                   "consts": [[hx(c), opt(t)] for c, t in row["consts"]]} for row in rc["recip"]],
    }
    if extra:
        if v2:
            head["tuples"] = [[i, [[[[col, hx(c)] for col, c in terms], hx(a)] for terms, a in comps]]
                              for i, comps in recip_tuples(rc)]
        head["uses_eta"] = v2
        head["digest"] = recip_digest(rc).hex()
    head["w_D"] = hxs(wit["w_D"])
    if v2:
        head["w_D_eta"] = hxs(proof["w_D_eta"])
    chal_keys = (["eta"] if v2 else []) + ["alpha", "rho", "lambda", "beta", "delta", "tau"]
    return {
        **head,
        "w_L": hxs(wit["w_L"]), "w_R": hxs(wit["w_R"]),
        "w_O": hxs(wit["w_O"]), "v": [hxs(v) for v in wit["v"]], "s": hxs(wit["s"]),
        "rand": {x: hxs(rnd[x]) for x in ("r_O", "r_L", "r_R", "l_S", "n_S")},
        "chal": {x: hx(chal[x]) for x in chal_keys},
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


def challenges(rng, eta=False):
    """The challenges of a reciprocal proof; eta (drawn last, so that the v1 draws are those
    of phase 5) only for a circuit that uses it."""
    c = {x: rng.randrange(1, L) for x in ("alpha", "rho", "lambda", "beta", "delta", "tau")}
    if eta:
        c["eta"] = rng.randrange(1, L)
    return c


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


def tuple_case(rng, name, fl, fm, violate=None):
    """A reciprocal form circuit with tuple poles (spec 4.1, protocol v2): N_p = 7 poles, N_m = 2,
    k = 2 inputs with N_v = 2 (f_l: copied into l_O by the first four linear rows; f_m: added
    to the first four numerators), w_O over all four slots. Poles 0, 1, 2: tuple poles with 3
    components (LCs with coefficients and repeated columns over the input copies and data in
    n_O / l_O, a constant solved; pole 0 reads an input copy exactly, pole 2 has a constant
    component), looked up in a public table of 4 rows of 3 random scalars (pole 0 and 2 on
    row 1, pole 1 on row 3), multiplicities in l_L / n_O / l_O, and constants on row 0 with the
    pole polynomials T_0 (length 3) and T_0 || 0 (length 4). Row 2 mixes the free pole 4
    (value z, numerator copied to l_L, public pole (z)) with the 2-component tuple poles 3 and
    5 (equal tuples, coefficient 2 on w_P,5), public poles (u_0, u_1) and (u_0, u_1, 0), and a
    pole-free term. Row 3: pole 6, a tuple pole with one component, against the public pole
    (x_6, 0). Row 4: public poles only (lengths 1, 2, 3). Ordinary rows read w_P, w_R and the
    tuple poles' w_D (so they hold at the drawn (eta, alpha) only); w_R and the two l_R
    elements are solved after (eta, alpha). w_D holds random placeholders at the tuple poles.
    violate: "component" (pole 1's last constant + 1: not a row of the table) or
    "multiplicity" (m_3 + 1)."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    np_, nm, nv, k, nlin = 7, 2, 2, 2, 9
    nm2 = np_ + nm
    Lc = lambda t: np_ + t  # noqa: E731
    P = lambda i: nm2 + i  # noqa: E731
    R = lambda t: nm2 + np_ + t  # noqa: E731
    O = lambda i: 2 * nm2 + i  # noqa: E731
    # w_O: 0-3 input copies (l_O), 4-9 data (n_O / l_O), 10-13 the table multiplicities,
    # 14 the coefficient of (u_0, u_1), 15 the numerator of pole 4, 16 that of pole 6, 17 and
    # 18 equal values (row 4), 19 and 20 l_R pivots
    kinds = (["lO"] * 4 + ["nO", "lO", "nO", "lO", "nO", "lO"] + ["lL", "lL", "nO", "lO"]
             + ["lL", "lL", "nO", "lO", "lL", "lR", "lR"])
    no = len(kinds)
    avail = {X: rng.sample(range(nm2 if X == "nO" else nlin), kinds.count(X)) for X in SLOTS}
    partition = [[X, avail[X].pop()] for X in kinds]
    v = [[s() for _ in range(nv)] for _ in range(k)]
    wv = [x for vi in v for x in vi]
    w_O = [0] * no
    w_O[0:4] = wv
    for e in range(4, 10):
        w_O[e] = s()
    w_O[17] = w_O[18] = s()

    def comp(target, cols):
        terms = [(O(e), s()) for e in cols]
        return (terms, (target - sum(c * w_O[col - O(0)] for col, c in terms)) % L)

    pick = lambda n: rng.sample(range(10), n)  # noqa: E731
    T = [[s() for _ in range(3)] for _ in range(4)]
    T[1][0] = wv[0]
    u, z, x6 = [s(), s()], s(), s()
    e5 = rng.randrange(10)
    tuples = [
        (0, [([(O(0), 1)], 0), comp(T[1][1], pick(2)), comp(T[1][2], pick(3))]),
        (1, [comp(T[3][0], pick(1)), comp(T[3][1], pick(2)), comp(T[3][2], pick(2))]),
        (2, [comp(T[1][0], pick(2)), ([], T[1][1]), comp(T[1][2], pick(1))]),
        (3, [comp(u[0], pick(2)), comp(u[1], pick(1))]),
        (5, [comp(u[0], [e5, e5]), comp(u[1], pick(3))]),
        (6, [comp(x6, pick(2))]),
    ]
    if violate == "component":
        terms, a = tuples[1][1][2]
        tuples[1][1][2] = (terms, (a + 1) % L)
    w_D = [s() for _ in range(np_)]  # placeholders at the tuple poles (ignored)
    w_D[4] = z
    w_L = [s() for _ in range(nm)]
    num_cols = [O(e) for e in range(10)] + [Lc(t) for t in range(nm)] + [4, O(17)]
    rc = {"n_p": np_, "n_m": nm, "n_o": no, "n_v": nv, "n_lin": nlin, "k": k,
          "f_l": fl, "f_m": fm, "partition": partition, "tuples": tuples,
          "w_n": [[(col, s()) for col in rng.sample(num_cols, 2)] for _ in range(np_)],
          "a_n": [s() for _ in range(np_)]}
    wit = {"w_D": w_D, "w_L": w_L, "w_R": [0] * nm, "w_O": w_O, "v": v,
           "s": [s() for _ in range(k)]}
    num = recip_numerators(rc, wit)  # W_n reads no tuple pole: independent of eta
    on_row = {0: 1, 1: 3, 2: 1}
    for r in range(4):
        w_O[10 + r] = sum(num[i] for i, rr in on_row.items() if rr == r) % L
    if violate == "multiplicity":
        w_O[13] = (w_O[13] + 1) % L
    K, c1, c2, c3, d = s(), s(), s(), s(), s()
    w_O[14] = (num[3] + 2 * num[5] - K) % L
    w_O[15] = num[4]
    w_O[16] = num[6]
    sp = [s() for _ in range(4)]
    rc["recip"] = [
        {"terms": [(P(i), 1, None) for i in range(3)] + [(O(10 + r), L - 1, T[r]) for r in range(4)],
         "consts": [(5, T[0]), (L - 5, T[0] + [0])]},
        {"terms": [(P(3), 1, None), (P(4), 1, None), (P(5), 2, None), (O(14), L - 1, u),
                   (O(15), L - 1, [z]), (O(5), c1, None)],
         "consts": [(-K % L, u + [0]), (-c1 * w_O[5] % L, None)]},
        {"terms": [(P(6), 1, None), (O(16), L - 1, [x6, 0]), (Lc(0), c2, None)],
         "consts": [(-c2 * w_L[0] % L, None)]},
        {"terms": [(O(17), 1, sp[:2]), (O(18), L - 1, sp[:2])],
         "consts": [(c3, sp[:3]), (-c3 % L, sp[:3]), (d, [sp[3]]), (-d % L, [sp[3], 0, 0])]},
    ]
    chal = challenges(rng, eta=True)
    wit_e = recip_eta_witness(rc, wit, chal["eta"])
    w_P = [x * inv(chal["alpha"] + dd) % L for x, dd in zip(num, wit_e["w_D"])]
    init = list(range(nm2)) + [O(e) for e in range(no) if kinds[e] != "lR"]
    w_m, a_m, w_R = [], [], [0] * nm
    for t in range(nm):
        cols = rng.sample(init, 2) + [P(rng.randrange(np_))] + ([R(t - 1)] if t else [0])
        row = [(col, s()) for col in cols]
        w_m.append(row)
        a_m.append(s())
        w = wit_e["w_D"] + w_L + w_P + w_R + w_O
        rhs = (sum(x * w[col] for col, x in row) + fm * (wv[np_ + t] if np_ + t < len(wv) else 0)
               + a_m[t]) % L
        w_R[t] = rhs * inv(w_L[t]) % L
    w_l, a_l = [], []
    if fl:
        for t in range(k * nv):
            w_l.append([(O(t), L - 1)])  # v_t - c_t = 0
            a_l.append(0)
    for pivot in (None, 19, 20):
        row = [(col, s()) for col in rng.sample(init, 2)]
        if pivot is not None:
            row += [(P(rng.randrange(np_)), s()), (R(rng.randrange(nm)), s()), (1, s()),
                    (O(pivot), s())]
        rng.shuffle(row)
        w = wit_e["w_D"] + w_L + w_P + w_R + w_O
        rest = sum(x * w[col] for col, x in row) % L
        if pivot is None:
            a_l.append(-rest % L)
        else:
            a_l.append(s())
            cp = dict((col, x) for col, x in row)[O(pivot)]
            w_O[pivot] = -(rest + a_l[-1]) * inv(cp) % L
        w_l.append(row)
    rc.update({"n_l": len(w_l), "w_m": w_m, "a_m": a_m, "w_l": w_l, "a_l": a_l})
    wit["w_R"] = w_R
    wit["chal"] = chal
    return rc, wit


def small_tuple_case(rng, delta, eta=None):
    """One tuple pole (x_0, x_1) = (w_O,0 + delta_0, w_O,1 + delta_1) with (w_O,0, w_O,1) =
    (3, 5) in n_O and l_O, numerator 1, and the reciprocal row w_P,0 - 1/(X + (3, 5)) = 0; plus an
    input copied by a linear row (f_l = 1) and one multiplication. delta = (16, -1) packs to the
    row with base 16 (19 + 16*4 = 3 + 16*5) but is not the row. eta overrides the challenge."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    np_, nm = 1, 1
    nm2 = np_ + nm
    P = lambda i: nm2 + i  # noqa: E731
    O = lambda i: 2 * nm2 + i  # noqa: E731
    vv, wl, wr = s(), s(), s()
    rc = {"n_p": np_, "n_m": nm, "n_o": 4, "n_v": 1, "n_lin": 2, "k": 1, "n_l": 1, "f_l": 1,
          "f_m": 0, "partition": [["nO", 0], ["lO", 0], ["lO", 1], ["nO", 1]],
          "tuples": [(0, [([(O(0), 1)], delta[0] % L), ([(O(1), 1)], delta[1] % L)])],
          "w_n": [[]], "a_n": [1], "w_m": [[(O(3), 1)]], "a_m": [0],
          "w_l": [[(O(2), L - 1)]], "a_l": [0],
          "recip": [{"terms": [(P(0), 1, None)], "consts": [(L - 1, [3, 5])]}]}
    chal = challenges(rng, eta=True)
    if eta is not None:
        chal["eta"] = eta
    wit = {"w_D": [s()], "w_L": [wl], "w_R": [wr], "w_O": [3, 5, vv, wl * wr % L], "v": [[vv]],
           "s": [s()], "chal": chal}
    return rc, wit


def public_poly_case(rng):
    """No tuple pole: protocol v2 because of public poles of length 2 and 3. A free pole p with
    numerator 3 against the public pole (p); a multiplicity M in n_O on the pole (a, b) against
    the constant -M on (a, b); constants on (c), (c, 0, 0) cancelling; an input copied (f_l = 1)
    and one multiplication."""
    s = lambda: rng.randrange(1, L)  # noqa: E731
    p, a, b, c, M, cc, vv, wl, wr = (s() for _ in range(9))
    O = lambda i: 4 + i  # noqa: E731
    rc = {"n_p": 1, "n_m": 1, "n_o": 3, "n_v": 1, "n_lin": 1, "k": 1, "n_l": 1, "f_l": 1,
          "f_m": 0, "partition": [["nO", 1], ["lO", 0], ["nO", 0]],
          "w_n": [[]], "a_n": [3], "w_m": [[(O(2), 1)]], "a_m": [0],
          "w_l": [[(O(1), L - 1)]], "a_l": [0],
          "recip": [{"terms": [(2, 1, None)], "consts": [(L - 3, [p])]},
                    {"terms": [(O(0), 1, [a, b])], "consts": [(-M % L, [a, b])]},
                    {"terms": [], "consts": [(cc, [c]), (-cc % L, [c, 0, 0])]}]}
    wit = {"w_D": [p], "w_L": [wl], "w_R": [wr], "w_O": [M, vv, wl * wr % L], "v": [[vv]],
           "s": [s()], "chal": challenges(rng, eta=True)}
    return rc, wit


def recip_v2_edge_checks(rng):
    """alpha = -w_D,i for a tuple pole (at eta) makes the prover fail; alpha = -t(eta) for a
    public pole polynomial makes the circuit uncompilable. eta = 0 compiles."""
    rc, wit = small_tuple_case(rng, (0, 0))
    chal = wit.pop("chal")
    rnd = {"r_O": [1] * 6, "r_L": [1] * 5, "r_R": [1] * 4, "l_S": [1] * 2, "n_S": [1] * 2}
    chal["alpha"] = -(3 + 5 * chal["eta"]) % L  # = -w_D,0 = -t(eta) for t = (3, 5)
    try:
        recip_prove(rc, wit, rnd, chal, [1] * wnla_rounds(9, 2)[0])
        raise AssertionError("prover accepted alpha = -w_D,i")
    except ReciprocalError:
        pass
    try:
        recip_compile(rc, chal["alpha"], chal["eta"])
        raise AssertionError("compiled with alpha = -t(eta)")
    except ReciprocalError:
        pass
    recip_compile(rc, chal["alpha"], 0)


def reciprocal_v2_cases(rng):
    """Circuits that use eta (spec 4.1, protocol v2)."""
    cases = []

    def run(name, rc, wit, expect, ident=None):
        entry = recip_run(rng, name, rc, wit, expect, extra=True)
        assert entry["uses_eta"]
        recip_v2_self_check(rc, wit, random.Random(name), expect if ident is None else ident)
        cases.append(entry)

    for fl, fm in ((1, 0), (1, 1), (0, 1)):
        name = f"tuple-lookup-f{fl}{fm}"
        run(name, *tuple_case(rng, name, fl, fm), True)
    run("tuple-small-2col", *small_tuple_case(rng, (0, 0)), True)
    run("public-poles-only-v2", *public_poly_case(rng), True)
    # the bad challenges of the compression (spec 4.7): eta = 16 makes (x_0 + 16, x_1 - 1)
    # equal to (x_0, x_1), eta = 0 ignores x_1; nothing special-cases them (spec 4.3)
    run("eta-16-base16-collision", *small_tuple_case(rng, (16, L - 1), eta=16), True, ident=False)
    run("eta-0-collision", *small_tuple_case(rng, (0, 7), eta=0), True, ident=False)
    # unsatisfied
    name = "bad-tuple-wrong-component"
    run(name, *tuple_case(rng, name, 1, 0, violate="component"), False)
    name = "bad-tuple-multiplicity"
    run(name, *tuple_case(rng, name, 1, 1, violate="multiplicity"), False)
    run("bad-tuple-base16-collision", *small_tuple_case(rng, (16, L - 1)), False)
    recip_v2_edge_checks(rng)
    return cases


def reciprocal_cases(rng):
    cases = []
    # range proofs: bases 2, 4, 16; inline (n_O) and shared (l_L); values incl. 0 and b^n - 1
    for b, n in ((2, 8), (4, 8), (16, 16)):
        top = b**n - 1
        for layout, vals in (("inline", (0, rng.randrange(top))), ("shared", (top, rng.randrange(top)))):
            for v in vals:
                name = f"range-b{b}-n{n}-{layout}-v{'max' if v == top else v}"
                cases.append(recip_run(rng, name, *range_case(rng, name, b, n, layout, v), True,
                                       extra=True))
    # multi-asset balance with range proofs of the amounts (base 4, 3 digits)
    txs = [(40, 0, 0), (25, 1, 0), (10, 0, 0), (50, 0, 1), (25, 1, 1)]
    cases.append(recip_run(rng, "mact-balanced", *mact_case(rng, "mact-balanced", txs, 4, 3), True,
                           extra=True))
    # generic mixed circuits
    for fl, fm in ((1, 1), (1, 0), (0, 1)):
        name = f"generic-f{fl}{fm}"
        cases.append(recip_run(rng, name, *generic_case(rng, name, fl, fm), True, extra=True))
    # unsatisfied
    name = "bad-range-digit-eq-base"  # v = 4^4 with digits (4, 3, 3, 3), best multiplicities
    cases.append(recip_run(rng, name, *range_case(rng, name, 4, 4, "inline", 256, digits=[4, 3, 3, 3]),
                           False, extra=True))
    name = "bad-range-wrong-multiplicity"
    cases.append(recip_run(rng, name, *range_case(rng, name, 2, 8, "shared", 77, mult_delta=(0, 1)),
                           False, extra=True))
    txs = [(40, 0, 0), (25, 1, 0), (10, 0, 0), (51, 0, 1), (25, 1, 1)]
    cases.append(recip_run(rng, "bad-mact-unbalanced",
                           *mact_case(rng, "bad-mact-unbalanced", txs, 4, 3), False,
                           extra=True))
    name = "bad-generic-numerator"
    cases.append(recip_run(rng, name, *generic_case(rng, name, 1, 1, violate=True), False, extra=True))
    cases += reciprocal_v2_cases(rng)
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

    def table(self, rows):
        return self._op({"op": "table", "rows": rows})

    def lookup(self, t, tup):
        return self._op({"op": "lookup", "table": t, "tuple": tup})

    def lookup_value(self, t, v):
        return self._op({"op": "lookup_value", "table": t, "v": v})

    def reciprocal(self, m, terms, public=()):
        return self._op({"op": "reciprocal", "m": m,
                         "terms": [{"num": n, "tuple": t} for n, t in terms],
                         "public": [{"coeff": c, "row": r} for c, r in public]})


def builder_case(rng, name, P, expect=True, uses_eta=None):
    """Replay the program from its JSON, finalize, lower (7.6), check, prove (recip_run).
    uses_eta: the expected protocol when it differs from the rule of spec 7.6 (an m >= 2
    argument with empty public coefficients only, see bld_uses_eta)."""
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
        # the verifier's lowering exists: its protocol and digest
        assert recip_uses_eta(rc_v) == bld_uses_eta(fin_v)
        base["uses_eta"] = recip_uses_eta(rc_v)
        base["digest"] = recip_digest(rc_v).hex()
        return base
    assert expect != "prover_error", name
    rc, wit = bld_lower(b, fin)
    assert rc == rc_v
    v2 = recip_uses_eta(rc)
    if uses_eta is None:
        assert v2 == bld_uses_eta(fin), name
    else:
        assert v2 == uses_eta != bld_uses_eta(fin), name
    costs = bld_costs(b, fin)
    assert costs["bppp_gates"] == rc["n_p"] + rc["n_m"]
    sem = bld_semantic(b, fin)
    assert sem == expect, (name, sem)
    eta = rng.randrange(1, L) if v2 else None
    recip_ok, ord_ok = recip_satisfied(rc, wit, rng.randrange(1, L), eta)
    assert (recip_ok and ord_ok) == sem, (name, recip_ok, ord_ok)
    bld_agreement_check(b, random.Random(name))
    wit["chal"] = challenges(rng, eta=v2)
    entry = recip_run(rng, name, rc, wit, expect, extra=True)
    if v2:
        assert recip_v2_self_check(rc, wit, random.Random(name + "/v2")) == sem
    del entry["name"]
    return {**base, "costs": costs, **entry}


def builder_cases(rng):
    s = lambda: rng.randrange(1, L)  # noqa: E731
    cases = []

    def add(name, P, expect=True):
        cases.append(builder_case(rng, name, P, expect))

    def range_table(P, w):
        return P.table([[i] for i in range(2**w)])

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
    P.reciprocal(1, [(lc(V0), [lc(W1)]), (lc((V0, L - 1)), [lc(V1)]),
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
    t0 = P.table([[0, 1], [1, 2]])
    t1 = P.table([[1], [2], [2], [5], [7]])
    t2 = P.table([[31], [0]])
    t3 = range_table(P, 2)
    P.lookup_value(t1, 2)
    P.lookup_value(t3, 3)
    P.lookup_value(t1, 2)
    P.lookup_value(t1, 5)
    y = P.witness(7)
    P.lookup(t1, [lc(y)])
    assert (t0, t2) == (0, 2)
    add("tables-duplicate-and-unused", P)

    # multi-column tables: XOR on 2-bit values, a split table; components with merged
    # coefficients, a constant, a variable merged to zero, a + 4b (tuple poles, protocol v2)
    P = Prog()
    tr = range_table(P, 2)
    A = P.lookup_value(tr, 2)
    B = P.lookup_value(tr, 3)
    C = P.witness(1)
    P.lookup(tr, [lc(C)])
    tx = P.table([[i, j, i ^ j] for i in range(4) for j in range(4)])
    P.lookup(tx, [lc(A), lc(B), lc(C)])
    P.lookup(tx, [lc((A, 2), (A, L - 1)), lc(B), lc(C)])
    P.lookup(tx, [lc(1), lc(B), lc(A)])
    U = P.witness(s())
    P.lookup(tx, [lc(A, U, (U, L - 1)), lc(B), lc(C)])
    ts = P.table([[n, n & 3, n >> 2] for n in range(16)])
    P.lookup(ts, [lc(A, (B, 4)), lc(A), lc(B)])
    P.lookup(ts, [lc((A, 4), 1), lc(1), lc(A)])
    add("xor-and-split-tables", P)

    # memory-style permutation, 2 components: writes added, reads subtracted, public terms
    # with a constant coefficient, with MultiplierRight + constant (copy), with
    # MultiplierLeft; a numerator with MultiplierRight (copy); a component MultiplierRight
    # (copy, m >= 2)
    P = Prog()
    tr = range_table(P, 4)
    Lm, Rm, Om = P.allocate_multiplier(5, 3)
    P.lookup(tr, [lc(Rm)])
    P.lookup(tr, [lc(Lm)])
    a0, v0 = P.lookup_value(tr, 1), P.lookup_value(tr, 9)
    a1, v1 = P.lookup_value(tr, 2), P.lookup_value(tr, 4)
    P.reciprocal(2,
                 [(lc(1), [lc(a0), lc(v0)]), (lc(Rm), [lc(a1), lc(v1)]),
                  (lc(L - 1), [lc(a1), lc(v1)]), (lc((Lm, L - 1)), [lc(Rm), lc(v1)])],
                 [(lc(L - 1), [1, 9]), (lc((Rm, L - 1), 1), [2, 4]), (lc(Lm), [3, 4])])
    add("memory-permutation-2col", P)

    # MACT-style balance: amounts (committed) as numerators, asset types as free poles
    # (one committed, one a witness)
    P = Prog()
    t0, t1 = s(), s()
    In0, In1 = P.commit(100, s()), P.commit(50, s())
    Out0, Out1, Out2 = P.commit(70, s()), P.commit(30, s()), P.commit(50, s())
    T0 = P.commit(t0, s())
    T1 = P.witness(t1)
    P.reciprocal(1, [(lc(In0), [lc(T0)]), (lc(In1), [lc(T1)]), (lc((Out0, L - 1)), [lc(T0)]),
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
    # coefficient, a witness sum, a zero-constant coefficient, an empty coefficient), m = 2
    P = Prog()
    av = s()
    A, B = P.witness(av), P.witness(-(av + 2) % L)
    P.reciprocal(1, [])
    P.reciprocal(2, [], [(lc(2), [1, 2]), (lc(A, B), [1, 2]), (lc(0), [7, 31]),
                         (lc(), [0, 0])])
    add("empty-and-public-only-arguments", P)

    # -- tuples without bounds (spec 7.3): the components are arbitrary field elements
    # a two-column table with large entries, looked up by fresh witnesses equal to the row
    # values (no range lookups at all) and by LCs with coefficients and constants
    P = Prog()
    rows = [[U64 - 1, 7], [123456789, 2**63], [0, 0], [U64 - 1, 8]]
    t2c = P.table(rows)
    X, Y = P.witness(U64 - 1), P.witness(8)
    P.lookup(t2c, [lc(X), lc(Y)])
    Z = P.witness(s())
    P.lookup(t2c, [lc((Z, 3), (Z, L - 3), 123456789), lc((Y, 2**60), 0)])
    P.lookup(t2c, [lc(), lc((X, 0))])
    P.lookup(t2c, [lc(X), lc(Y, L - 1)])
    add("lookup-2col-unbounded-components", P)

    # a 3-column reciprocal argument over large field elements: equal tuples written with
    # different LCs cancel (weighted by a committed input), a swapped tuple cancels with
    # itself, and a small tuple against a public row
    P = Prog()
    V0 = P.commit(s(), s())
    a_, b_, c_ = s(), s(), s()
    A, B, C = P.witness(a_), P.witness(b_), P.witness(c_)
    D = P.witness(s())
    One, Two = P.witness(1), P.witness(2)
    P.reciprocal(3, [(lc(1), [lc(A), lc(B), lc(C)]),
                     (lc(L - 1), [lc(A, (D, 0)), lc((B, 2), (B, L - 1)), lc(C)]),
                     (lc(V0), [lc(B), lc(A), lc(C)]),
                     (lc((V0, L - 1)), [lc((A, 0), B), lc(A), lc((C, 5), (C, L - 4), 0)]),
                     (lc(V0, 3), [lc(One), lc(Two), lc(3)])],
                 [(lc((V0, L - 1), L - 3), [1, 2, 3])])
    add("reciprocal-3col-field-components", P)

    # components reading MultiplierLeft and MultiplierRight (copies), MultiplierOutput and
    # Committed (no copy), constants and coefficients; an m = 1 argument and a one-column
    # lookup next to them (free poles: their pole rows read w_L, w_R directly, no copy)
    P = Prog()
    V0 = P.commit(6, s())
    L0, R0, O0 = P.multiply(lc(V0), lc(7))     # 6 * 7 = 42
    L1 = P.allocate(3)                          # pending: R1 = O1 = 0
    tq = P.table([[42, 6, 7], [6, 7, 42], [0, 3, 1]])
    P.lookup(tq, [lc(O0), lc(L0), lc(R0)])
    P.lookup(tq, [lc((L0, 1)), lc(R0), lc(O0)])
    P.lookup(tq, [lc((R0, 0), ("R", 1)), lc(L1), lc(V0, (R0, L - 1), 2)])
    tr = P.table([[i] for i in range(8)])
    P.lookup(tr, [lc(R0)])
    P.lookup(tr, [lc(L1, 4)])
    W5 = P.witness(5)
    P.reciprocal(1, [(lc(R0), [lc(L0, (R0, 0))]), (lc((R0, L - 1)), [lc(V0)])])
    P.reciprocal(2, [(lc(R0, (L0, 2)), [lc(L1), lc(W5)]), (lc(L - 19), [lc(3), lc((W5, 1))])],
                 [(lc(R0), [3, 5]), (lc((R0, L - 1), (O0, 0)), [3, 5])])
    add("mixed-m1-and-tuple-arguments-copies", P)

    # a public-only argument with m = 3 (the public rows as pole polynomials of length 3)
    P = Prog()
    W0 = P.witness(s())
    W1 = P.witness(P.val(lc(W0)))
    P.reciprocal(3, [], [(lc(W0), [1, 2, 3]), (lc((W1, L - 1)), [1, 2, 3]),
                         (lc(2), [5, 6, 0]), (lc(L - 2), [5, 6, 0])])
    add("public-only-3col-argument", P)

    # an m = 2 argument whose public coefficients are all empty LCs: it lowers to an empty
    # reciprocal row with no pole, so the lowered circuit does not use eta by spec 4.1, while
    # spec 7.6 says "uses eta exactly when A has an argument with m >= 2" (reported; we follow
    # the circuit, 4.1: protocol v1)
    P = Prog()
    W0 = P.witness(4)
    P.reciprocal(2, [], [(lc(), [1, 2]), (lc(), [3, 4])])
    P.reciprocal(1, [(lc(1), [lc(W0)])], [(lc(L - 1), [4])])
    cases.append(builder_case(rng, "public-2col-empty-coefficients-v1", P, True, uses_eta=False))

    # -- unsatisfied
    P = Prog()
    av, bv = s(), s()
    A, B, C = P.witness(av), P.witness(bv), P.witness(av * bv + 1)
    P.product(lc(A), lc(B), lc(C))
    add("bad-product", P, False)

    P = Prog()
    A, B = P.witness(s()), P.witness(s())
    P.reciprocal(1, [(lc(1), [lc(A)]), (lc(L - 1), [lc(B)])])
    add("bad-reciprocal-not-vanishing", P, False)

    P = Prog()
    tr = range_table(P, 2)
    A, B = P.lookup_value(tr, 1), P.lookup_value(tr, 2)
    P.reciprocal(2, [(lc(1), [lc(A), lc(B)]), (lc(L - 1), [lc(B), lc(A)])],
                 [(lc(1), [1, 2]), (lc(L - 1), [2, 1])])
    add("bad-reciprocal-public-swapped", P, False)

    # (x_0 + 16, x_1 - 1) against the row (x_0, x_1): equal packings with base 16, distinct
    # tuples
    P = Prog()
    A, B = P.witness(3 + 16), P.witness(5 - 1)
    P.reciprocal(2, [(lc(1), [lc(A), lc(B)])], [(lc(L - 1), [3, 5])])
    add("bad-reciprocal-2col-base16-collision", P, False)

    P = Prog()
    A, B, C = P.witness(s()), P.witness(s()), P.witness(s())
    P.reciprocal(3, [(lc(1), [lc(A), lc(B), lc(C)]), (lc(L - 1), [lc(A), lc(B), lc(C, 1)])])
    add("bad-reciprocal-3col-one-component-off", P, False)

    # -- prover errors (a lookup equal to no row)
    P = Prog()
    t = range_table(P, 3)
    P.lookup_value(t, 9)
    add("prover-error-lookup-value", P, "prover_error")

    P = Prog()
    tr = range_table(P, 2)
    A, B, C = P.lookup_value(tr, 1), P.lookup_value(tr, 2), P.lookup_value(tr, 0)
    tx = P.table([[i, j, i ^ j] for i in range(4) for j in range(4)])
    P.lookup(tx, [lc(A), lc(B), lc(C)])
    add("prover-error-xor-tuple", P, "prover_error")

    # (x_0 + 16, x_1 - 1) = (19, 4) packs with base 16 to the row (3, 5) of a table of all
    # pairs of 4-bit values, but is no row
    P = Prog()
    t44 = P.table([[i, j] for i in range(16) for j in range(16)])
    A, B = P.witness(3 + 16), P.witness(5 - 1)
    P.lookup(t44, [lc(A), lc(B)])
    add("prover-error-tuple-base16-collision", P, "prover_error")

    # -- construction errors (the failing operation is the last)
    def err(name, build):
        P = Prog()
        build(P)
        assert P.failed is not None
        add(name, P)

    def xor_setup(P):
        tr = range_table(P, 2)
        A, B = P.lookup_value(tr, 1), P.lookup_value(tr, 2)
        tx = P.table([[i, j, i ^ j] for i in range(4) for j in range(4)])
        return tr, A, B, tx

    err("err-empty-table", lambda P: P.fail("table", []))
    err("err-table-zero-columns", lambda P: P.fail("table", [[]]))

    def e_row_len(P):
        P.fail("table", [[1, 2], [3]])
    err("err-table-row-length", e_row_len)

    def e_lv_2col(P):
        t = P.table([[1, 1]])
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
        P.fail("reciprocal", 1, [(lc(V0, ("V", 1)), [lc(X)])])
    err("err-variable-does-not-exist-numerator", e_var_recip)

    def e_pub_len(P):
        tr, A, B, tx = xor_setup(P)
        P.fail("reciprocal", 2, [(lc(1), [lc(A), lc(B)])], [(lc(L - 1), [1])])
    err("err-public-row-length", e_pub_len)

    def e_recip_tuple_len(P):
        X = P.witness(1)
        P.fail("reciprocal", 2, [(lc(1), [lc(X), lc(X), lc(X)])])
    err("err-reciprocal-tuple-length", e_recip_tuple_len)

    def e_recip_zero(P):
        X = P.witness(1)
        P.reciprocal(1, [(lc(1), [lc(X)])], [(lc(L - 1), [1])])
        P.fail("reciprocal", 0, [])
    err("err-reciprocal-zero-columns", e_recip_zero)
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

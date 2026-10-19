#!/usr/bin/env python3
"""Writes tests/vectors/bppp/*.json from the reference (python3 ref/gen_vectors.py).
Deterministic: the same output on every run."""

import json
import os
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bppp_ref import (L, SLOTS, Sym, circuit_prove, circuit_self_check, wnla_commit,  # noqa: E402
                      wnla_prove, wnla_rounds, wnla_verify)

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


if __name__ == "__main__":
    main()

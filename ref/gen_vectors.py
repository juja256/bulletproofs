#!/usr/bin/env python3
"""Writes tests/vectors/bppp/*.json from the reference (python3 ref/gen_vectors.py).
Deterministic: the same output on every run."""

import json
import os
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bppp_ref import L, Sym, wnla_commit, wnla_prove, wnla_rounds, wnla_verify  # noqa: E402

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


if __name__ == "__main__":
    main()

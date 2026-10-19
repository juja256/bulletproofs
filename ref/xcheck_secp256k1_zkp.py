#!/usr/bin/env python3
"""Cross-check the reference's norm linear argument against secp256k1-zkp (Blockstream).

Runs `bppp_ref.wnla_prove` — the same function that generates our ristretto255 vectors —
over secp256k1 with secp256k1-zkp's transcript, point encoding and legacy layout, and
compares the proofs byte for byte with their prove vectors
(tests/vectors/bppp/secp256k1-zkp/norm_prove.json, from their test_vectors/prove.h).

    python3 ref/xcheck_secp256k1_zkp.py
"""

import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bppp_ref  # noqa: E402

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
VECTORS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "vectors", "bppp",
                       "secp256k1-zkp", "norm_prove.json")


class Pt:
    """A secp256k1 point in affine coordinates; x is None for the point at infinity."""

    __slots__ = ("x", "y")

    def __init__(self, x=None, y=None):
        self.x, self.y = x, y

    def __add__(self, o):
        if self.x is None:
            return o
        if o.x is None:
            return self
        if self.x == o.x:
            if (self.y + o.y) % P == 0:
                return Pt()
            lam = 3 * self.x * self.x * pow(2 * self.y, P - 2, P) % P
        else:
            lam = (o.y - self.y) * pow(o.x - self.x, P - 2, P) % P
        x = (lam * lam - self.x - o.x) % P
        return Pt(x, (lam * (self.x - x) - self.y) % P)

    def scale(self, k):
        k %= N
        r, a = Pt(), self
        while k:
            if k & 1:
                r = r + a
            a = a + a
            k >>= 1
        return r

    def ser33(self):
        if self.x is None:
            return b"\x00" * 33
        return bytes([2 | (self.y & 1)]) + self.x.to_bytes(32, "big")


def parse33(b):
    x = int.from_bytes(b[1:], "big")
    y = pow((x**3 + 7) % P, (P + 1) // 4, P)
    assert y * y % P == (x**3 + 7) % P, "not on the curve"
    return Pt(x, y if (y & 1) == (b[0] & 1) else P - y)


def ser_points(X, R):
    """secp256k1-zkp's 65-byte encoding of a round: sign bits of X and R, x(X), x(R)."""
    a, b = X.ser33(), R.ser33()
    return bytes([((a[0] & 1) << 1) | (b[0] & 1)]) + a[1:] + b[1:]


def main():
    doc = json.load(open(VECTORS))
    bppp_ref.use_field(N)
    G = Pt(GX, GY)
    gens = [parse33(bytes.fromhex(h)) for h in doc["gens"]]
    be = lambda h: int.from_bytes(bytes.fromhex(h), "big")  # noqa: E731
    ok = 0
    for i, case in enumerate(doc["cases"]):
        n, l, c = [be(x) for x in case["n"]], [be(x) for x in case["l"]], [be(x) for x in case["c"]]
        transcript = hashlib.sha256()

        def challenge(X, R):
            transcript.update(ser_points(X, R))
            t = transcript.copy()
            t.update((0).to_bytes(8, "little"))
            return int.from_bytes(t.digest(), "big") % N

        rounds, lf, nf = bppp_ref.wnla_prove(G, gens[len(n):len(n) + len(l)], gens[:len(n)], c, be(case["rho"]),
                                             l, n, challenge, legacy=True)
        proof = b"".join(ser_points(X, R) for X, R in rounds) + nf[0].to_bytes(32, "big") + lf[0].to_bytes(32, "big")
        same = proof.hex() == case["proof"]
        ok += same
        print(f"vector {i}: |n| = {len(n)}, |l| = {len(l)}, {len(rounds)} rounds: {'match' if same else 'DIFFERENT'}")
    print(f"{ok}/{len(doc['cases'])} secp256k1-zkp norm-argument proofs reproduced byte for byte")
    sys.exit(0 if ok == len(doc["cases"]) else 1)


if __name__ == "__main__":
    main()

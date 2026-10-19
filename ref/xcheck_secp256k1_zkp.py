#!/usr/bin/env python3
"""Cross-check the reference's norm linear argument against secp256k1-zkp (Blockstream).

Runs `bppp_ref.wnla_prove` — the same function that generates our ristretto255 vectors —
over secp256k1 with secp256k1-zkp's transcript, point encoding and legacy layout, and
compares the proofs byte for byte with their prove vectors
(tests/vectors/bppp/secp256k1-zkp/norm_prove.json, from their test_vectors/prove.h). Then
runs the reference's naive verifier `bppp_ref.wnla_verify` on their verify vectors
(norm_verify.json, from test_vectors/verify.h) and compares the verdicts; vector 6 pins the
rule for a frozen norm vector.

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
DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "vectors", "bppp", "secp256k1-zkp")


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

    def __eq__(self, o):
        return (self.x, self.y) == (o.x, o.y)

    def ser33(self):
        if self.x is None:
            return b"\x00" * 33
        return bytes([2 | (self.y & 1)]) + self.x.to_bytes(32, "big")


def parse33(b):
    x = int.from_bytes(b[1:], "big")
    y = pow((x**3 + 7) % P, (P + 1) // 4, P)
    assert y * y % P == (x**3 + 7) % P, "not on the curve"
    return Pt(x, y if (y & 1) == (b[0] & 1) else P - y)


def parse_round(in65):
    """secp256k1-zkp's parse of a 65-byte round (bppp_util.h): sign byte <= 3; an all-zero
    x encodes the point at infinity and then requires sign bit 0. Raises ValueError."""
    if in65[0] > 3:
        raise ValueError("sign byte")
    out = []
    for idx in (0, 1):
        xb, sign = in65[1 + 32 * idx:33 + 32 * idx], (in65[0] >> (1 - idx)) & 1
        if not any(xb):
            if sign:
                raise ValueError("infinity with sign bit")
            out.append(Pt())
            continue
        x = int.from_bytes(xb, "big")
        y2 = (x**3 + 7) % P
        y = pow(y2, (P + 1) // 4, P)
        if x >= P or y * y % P != y2:
            raise ValueError("not on the curve")
        out.append(Pt(x, y if (y & 1) == sign else P - y))
    return out


def ser_points(X, R):
    """secp256k1-zkp's 65-byte encoding of a round: sign bits of X and R, x(X), x(R)."""
    a, b = X.ser33(), R.ser33()
    return bytes([((a[0] & 1) << 1) | (b[0] & 1)]) + a[1:] + b[1:]


def be(h):
    return int.from_bytes(bytes.fromhex(h), "big")


def challenge_of(transcript, chunk):
    transcript.update(chunk)
    t = transcript.copy()
    t.update((0).to_bytes(8, "little"))
    return int.from_bytes(t.digest(), "big") % N


def verify_case(G, gens, case):
    """Verdict of the reference's naive verifier, with secp256k1-zkp's input checks."""
    c, b, rho = [be(x) for x in case["c"]], case["n_len"], be(case["rho"])
    a = len(c)
    pow2 = lambda x: x > 0 and x & (x - 1) == 0  # noqa: E731
    if not (pow2(a) and pow2(b)) or rho % N == 0:
        return False
    k = max(a.bit_length(), b.bit_length()) - 1
    proof = bytes.fromhex(case["proof"])
    if len(proof) != 65 * k + 64:
        return False
    cb = bytes.fromhex(case["commit"])
    try:
        C = parse33(cb) if any(cb) else Pt()
        transcript, rounds, gammas = hashlib.sha256(), [], []
        for r in range(k):
            chunk = proof[65 * r:65 * r + 65]
            rounds.append(tuple(parse_round(chunk)))
            gammas.append(challenge_of(transcript, chunk))
    except (ValueError, AssertionError):
        return False
    nf, lf = int.from_bytes(proof[65 * k:65 * k + 32], "big"), int.from_bytes(proof[65 * k + 32:], "big")
    if nf >= N or lf >= N:
        return False
    return bppp_ref.wnla_verify(G, gens[b:b + a], gens[:b], c, rho, C, rounds, [lf], [nf], gammas, legacy=True)


def main():
    doc = json.load(open(os.path.join(DIR, "norm_prove.json")))
    bppp_ref.use_field(N)
    G = Pt(GX, GY)
    gens = [parse33(bytes.fromhex(h)) for h in doc["gens"]]
    ok = 0
    for i, case in enumerate(doc["cases"]):
        n, l, c = [be(x) for x in case["n"]], [be(x) for x in case["l"]], [be(x) for x in case["c"]]
        transcript = hashlib.sha256()

        def challenge(X, R):
            return challenge_of(transcript, ser_points(X, R))

        rounds, lf, nf = bppp_ref.wnla_prove(G, gens[len(n):len(n) + len(l)], gens[:len(n)], c, be(case["rho"]),
                                             l, n, challenge, legacy=True)
        proof = b"".join(ser_points(X, R) for X, R in rounds) + nf[0].to_bytes(32, "big") + lf[0].to_bytes(32, "big")
        same = proof.hex() == case["proof"]
        ok += same
        print(f"vector {i}: |n| = {len(n)}, |l| = {len(l)}, {len(rounds)} rounds: {'match' if same else 'DIFFERENT'}")
    print(f"{ok}/{len(doc['cases'])} secp256k1-zkp norm-argument proofs reproduced byte for byte")
    vdoc = json.load(open(os.path.join(DIR, "norm_verify.json")))
    vgens = [parse33(bytes.fromhex(h)) for h in vdoc["gens"]]
    vok = 0
    for i, case in enumerate(vdoc["cases"]):
        got = verify_case(G, vgens, case)
        vok += got == bool(case["result"])
        print(f"verify vector {i}: expected {case['result']}, reference {int(got)}")
    print(f"{vok}/{len(vdoc['cases'])} secp256k1-zkp norm-argument verdicts reproduced")
    sys.exit(0 if ok == len(doc["cases"]) and vok == len(vdoc["cases"]) else 1)


if __name__ == "__main__":
    main()

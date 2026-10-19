#!/usr/bin/env python3
"""Spec-level reference of the BP++ protocols, written from docs/bppp/spec.md and the paper
(ePrint 2022/510), not from the Rust code.

Pure field arithmetic modulo the ristretto255 group order. Group elements are symbolic: a
point is a map {generator: coefficient} over the named base generators ("G", 0), ("H", i)
and ("N", i). Challenges are inputs, so the vectors check the protocol algebra; Fiat-Shamir
and point encoding are checked separately (transcript tests in Rust).
"""

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
    return G.scale(v) + msm(l, H) + msm(n, N)


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


def wnla_verify(G, H, N, c, rho, C, rounds, l, n, gammas):
    """Naive recursive verifier (section 4.3): fold everything, check the opening."""
    mu = rho * rho % L
    k, a, b = wnla_rounds(len(H), len(N))
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

"""SHA-256 transcript of the bulletproofs fork (docs/sha256-transcript.md): an independent
reference on hashlib.

    python3 -I ref/sha256_transcript.py                      # write the KATs
    python3 -I ref/sha256_transcript.py --check-trace F...   # replay traces of full proofs
"""
import hashlib
import json
import os
import struct
import sys

TAG = b"bulletproofs/transcript/sha256/v1"
APPEND, CHALLENGE, RNG = b"\x41", b"\x43", b"\x52"
MAX_CHALLENGE_BYTES = 2048
N_SECP256K1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
L_RISTRETTO = 2**252 + 27742317777372353535851937790883648493
HERE = os.path.dirname(os.path.abspath(__file__))
KAT_PATH = os.path.join(HERE, "..", "tests", "vectors", "transcript", "sha256.json")


def le32(n):
    return struct.pack("<I", n)


def le64(n):
    return struct.pack("<Q", n)


class Sha256Transcript:
    def __init__(self, label):
        self.ctx = hashlib.sha256(init_block())
        self.append_message(b"dom-sep", label)

    def append_message(self, label, msg):
        self.ctx.update(APPEND + le32(len(label)) + label + le32(len(msg)) + msg)

    def append_u64(self, label, x):
        self.append_message(label, le64(x))

    def challenge_bytes(self, label, n):
        assert 1 <= n <= MAX_CHALLENGE_BYTES
        self.ctx.update(CHALLENGE + le32(len(label)) + label + le32(n))
        out = b""
        for i in range((n + 31) // 32):
            c = self.ctx.copy()
            c.update(le64(i))
            out += c.digest()
        return out[:n]

    def challenge_scalar(self, label, order, endian):
        return int.from_bytes(self.challenge_bytes(label, 64), endian) % order

    def rng_digest(self):
        c = self.ctx.copy()
        c.update(RNG)
        return c.digest()


def init_block():
    t = hashlib.sha256(TAG).digest()
    return t + t


# SHA-256 compression, only to print the midstate after the init block (hashlib hides it).
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]
IV = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]


def compress(state, block):
    rotr = lambda x, n: ((x >> n) | (x << (32 - n))) & 0xFFFFFFFF
    w = list(struct.unpack(">16I", block))
    for i in range(16, 64):
        s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
        s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
        w.append((w[i - 16] + s0 + w[i - 7] + s1) & 0xFFFFFFFF)
    a, b, c, d, e, f, g, h = state
    for i in range(64):
        t1 = (h + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) & 0xFFFFFFFF
        t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) & 0xFFFFFFFF
        a, b, c, d, e, f, g, h = (t1 + t2) & 0xFFFFFFFF, a, b, c, (d + t1) & 0xFFFFFFFF, e, f, g
    return [(x + y) & 0xFFFFFFFF for x, y in zip(state, [a, b, c, d, e, f, g, h])]


def midstate():
    return compress(IV, init_block())


def _self_check_compress():
    # SHA-256("abc") through the compression above, against hashlib
    block = b"abc" + b"\x80" + b"\x00" * 52 + struct.pack(">Q", 24)
    assert b"".join(struct.pack(">I", x) for x in compress(IV, block)) == hashlib.sha256(b"abc").digest()


def run_ops(label, ops):
    """Runs the ops of a KAT case; returns the outputs (hex)."""
    t = Sha256Transcript(label)
    out = []
    for op in ops:
        kind = op[0]
        if kind == "append":
            t.append_message(bytes.fromhex(op[1]), bytes.fromhex(op[2]))
        elif kind == "u64":
            t.append_u64(bytes.fromhex(op[1]), op[2])
        elif kind == "challenge":
            out.append(t.challenge_bytes(bytes.fromhex(op[1]), op[2]).hex())
        elif kind == "scalar_secp256k1":
            out.append(t.challenge_scalar(bytes.fromhex(op[1]), N_SECP256K1, "big").to_bytes(32, "big").hex())
        elif kind == "scalar_ristretto":
            out.append(t.challenge_scalar(bytes.fromhex(op[1]), L_RISTRETTO, "little").to_bytes(32, "little").hex())
        elif kind == "rng_digest":
            out.append(t.rng_digest().hex())
        else:
            raise ValueError(kind)
    return out


def kats():
    h = lambda b: b.hex()
    cases = []

    def case(name, label, ops):
        cases.append({"name": name, "label": h(label), "ops": ops, "outputs": run_ops(label, ops)})

    case("empty", b"", [["challenge", "", 32]])
    case("merlin_like", b"test", [["append", h(b"some label"), h(b"some data")], ["challenge", h(b"challenge"), 32]])
    ops = []
    for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 1000]:
        ops += [["append", h(b"m"), h(bytes(i % 251 for i in range(n)))], ["challenge", h(b"c"), 32]]
    case("block_boundaries", b"blocks", ops)
    case("lengths", b"lengths", [["challenge", h(b"c"), n] for n in [1, 31, 32, 33, 64, 65, 2048]])
    case("back_to_back", b"b2b", [["challenge", h(b"same"), 64], ["challenge", h(b"same"), 64]])
    case("u64", b"u64", [["u64", h(b"n"), 0], ["u64", h(b"n"), 2**64 - 1], ["challenge", h(b"c"), 32]])
    point = b"\x02" + bytes(range(1, 33))
    case("scalars", b"scalars", [["append", h(b"P"), h(point)], ["scalar_secp256k1", h(b"x")], ["scalar_ristretto", h(b"x")]])
    case("rng_digest", b"rng", [["append", h(b"m"), h(b"x")], ["rng_digest"], ["challenge", h(b"c"), 32]])
    return {
        "tag": TAG.decode(),
        "init_block": h(init_block()),
        "midstate": [f"{x:08x}" for x in midstate()],
        "r_secp256k1": f"{2**256 % N_SECP256K1:064x}",
        "cases": cases,
    }


def check_traces(paths):
    traces = challenges = 0
    for p in paths:
        v = json.load(open(p))
        t = Sha256Transcript(bytes.fromhex(v["label"]))
        for i, op in enumerate(v["trace"]):
            if op[0] == "append":
                t.append_message(bytes.fromhex(op[1]), bytes.fromhex(op[2]))
            elif op[0] == "challenge":
                got = t.challenge_bytes(bytes.fromhex(op[1]), op[2]).hex()
                if got != op[3]:
                    print(f"{p}: challenge mismatch at trace index {i}")
                    sys.exit(1)
                challenges += 1
            else:
                raise ValueError(op[0])
        traces += 1
    print(f"{traces} traces, {challenges} challenges, all match")


def main():
    _self_check_compress()
    if sys.argv[1:2] == ["--check-trace"]:
        check_traces(sys.argv[2:])
        return
    os.makedirs(os.path.dirname(KAT_PATH), exist_ok=True)
    with open(KAT_PATH, "w") as f:
        json.dump(kats(), f, indent=1)
        f.write("\n")


if __name__ == "__main__":
    main()

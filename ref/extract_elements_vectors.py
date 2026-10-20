#!/usr/bin/env python3
"""Extracts secp256k1-zkp's generator test vectors (src/modules/generator/tests_impl.h) to
tests/vectors/elements/generators.json: the Shallue–van de Woestijne map at t = +-i
(i = 0..16, test_shallue_van_de_woestijne) and generator_generate for the keys
[0; 31] || i, i = 1..32 (test_generator_generate). Reads the C file only.

    python3 -I ref/extract_elements_vectors.py [path/to/tests_impl.h]
"""

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT = os.path.join(HERE, "..", "..", "..", "..", "bs", "secp256k1-zkp", "src", "modules", "generator", "tests_impl.h")
OUT = os.path.join(HERE, "..", "tests", "vectors", "elements", "generators.json")


def points(src, function):
    """The SECP256K1_GE_STORAGE_CONST entries of the `results` array in `function`, as (x, y)
    hex strings (big-endian, 32 bytes each)."""
    body = src[src.index(f"static void {function}(void)"):]
    body = body[: body.index("};")]
    out = []
    for words in re.findall(r"SECP256K1_GE_STORAGE_CONST\(([^)]*)\)", body):
        w = [int(x, 16) for x in words.split(",")]
        assert len(w) == 16
        hx = "".join(f"{x:08x}" for x in w)
        out.append((hx[:64], hx[64:]))
    return out


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
    src = open(path).read()
    svdw = points(src, "test_shallue_van_de_woestijne")
    assert len(svdw) == 34
    gen = points(src, "test_generator_generate")
    assert len(gen) == 32
    p = 2**256 - 2**32 - 977
    data = {
        "source": "secp256k1-zkp src/modules/generator/tests_impl.h",
        "svdw": [
            {"t": f"{(-i) % p if s else i:064x}", "x": svdw[2 * i + s][0], "y": svdw[2 * i + s][1]}
            for i in range(17)
            for s in range(2)
        ],
        "generate": [
            {"key": f"{i:064x}", "x": x, "y": y} for i, (x, y) in zip(range(1, 33), gen)
        ],
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as f:
        json.dump(data, f, indent=1)
        f.write("\n")
    print(f"generators.json: {len(data['svdw'])} SvdW points, {len(data['generate'])} generators")


if __name__ == "__main__":
    main()

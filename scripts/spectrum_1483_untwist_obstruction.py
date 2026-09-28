#!/usr/bin/env python3
"""Recheck the small E1483 cubic-untwisting obstruction without a solver.

The independently kernel-checked proof is NoCubicUntwist.lean. This script
reproduces its finite certificate from a previously saved permutation cover.
It does not refute general FO-definability from E1483 to E1485.
"""

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check():
    record = json.loads((ROOT / "data/spectrum/1483_untwist_obstruction.json").read_text())
    original = json.loads((ROOT / record["source_file"]).read_text())
    table = original["extensions"]["examples"][record["example_index"]]["table"]
    n = len(table)
    assert n == 32
    assert all(len(row) == n and all(0 <= t < n for t in row) for row in table)
    lean = ROOT / "equational_theories/Spectrum/Equation1483/NoCubicUntwist.lean"
    packed = [int(value, 16) for value in re.findall(r"0x[0-9a-f]+", lean.read_text())]
    assert packed == [sum(t << (5 * y) for y, t in enumerate(row)) for row in table]
    op = lambda x, y: table[x][y]
    assert all(op(op(y, x), op(x, op(y, z))) == x
               for x in range(n) for y in range(n) for z in range(n))
    assert op(op(4, 4), op(4, op(8, 4))) != 4

    # Recipes show that images of two generators determine any endomorphism.
    reached = set(record["generators"])
    for z, x, y in record["recipes"]:
        assert x in reached and y in reached and z not in reached
        assert op(x, y) == z
        reached.add(z)
    assert reached == set(range(n))

    endos, surviving_pairs = [], []
    for a in range(n):
        for b in range(n):
            f = [None] * n
            for x, image in zip(record["generators"], [a, b]):
                f[x] = image
            for z, x, y in record["recipes"]:
                f[z] = op(f[x], f[y])
            if a != b and all(f[op(x, y)] == op(f[x], f[y])
                              for x, y in record["hom_relations"]):
                surviving_pairs.append((a, b))
            if all(f[op(x, y)] == op(f[x], f[y])
                   for x in range(n) for y in range(n)):
                endos.append(f)
    assert set(surviving_pairs) == {(27, 31), (24, 28)}
    identity, flip = list(range(n)), [x ^ 3 for x in range(n)]
    assert len(endos) == record["endomorphism_count"]
    assert sorted(endos) == sorted([identity, flip] +
                                  [[c] * n for c in record["constant_endomorphisms"]])
    assert all(f == identity for f in endos if all(f[f[f[x]]] == x for x in range(n)))

    # A different operation is E1485 and invariant under both automorphisms.
    # FiniteBridge turns this invariance into parameter-free FO-definability.
    companion = lambda x, y: 4 * (7 ^ ((x // 4) & (y // 4))) + 2 * (x % 2) + (y % 4) // 2
    assert all(0 <= companion(x, y) < n for x in range(n) for y in range(n))
    assert all(companion(companion(y, x), companion(x, companion(z, y))) == x
               for x in range(n) for y in range(n) for z in range(n))
    assert all(flip[companion(x, y)] == companion(flip[x], flip[y])
               for x in range(n) for y in range(n))
    print("Verified: E1483, eight endomorphisms, Aut=C2, no cubic untwist, FO E1485 companion.")


if __name__ == "__main__":
    check()

#!/usr/bin/env python3
"""Reconstruct Bennett's idempotent E63 model of order 32.

Source: F. E. Bennett, Quasigroup Identities and Mendelsohn Designs (1989),
Figure 1 and Lemma 5.13, DOI 10.4153/CJM-1989-017-0. Inflate the partial C3
quasigroup of type 2^4 by the four-point C3 quasigroup, fill its four eight-point
holes, then take left division to obtain E63. No model search is used.

With no arguments, print the packed table used by IdempotentSeeds.lean. With
--check-lean, also check that the Lean source contains exactly this certificate.
All algebraic and Latin-square conditions are checked before output.
"""

import argparse
from pathlib import Path


PARTIAL8 = [
    [None, 7, 3, 5, None, 2, 1, 6],
    [7, None, 0, 4, 6, None, 3, 2],
    [3, 0, None, 1, 5, 7, None, 4],
    [5, 4, 1, None, 2, 6, 0, None],
    [None, 6, 5, 2, None, 3, 7, 1],
    [2, None, 7, 6, 3, None, 4, 0],
    [1, 3, None, 0, 7, 4, None, 5],
    [6, 2, 4, None, 1, 0, 5, None],
]
C3_4 = [[0, 2, 3, 1], [2, 0, 1, 3], [3, 1, 0, 2], [1, 3, 2, 0]]
E63_8 = [
    [0, 2, 4, 6, 3, 1, 7, 5],
    [3, 1, 7, 5, 0, 2, 4, 6],
    [6, 4, 2, 0, 5, 7, 1, 3],
    [5, 7, 1, 3, 6, 4, 2, 0],
    [7, 5, 3, 1, 4, 6, 0, 2],
    [4, 6, 0, 2, 7, 5, 3, 1],
    [1, 3, 5, 7, 2, 0, 6, 4],
    [2, 0, 6, 4, 1, 3, 5, 7],
]


def check_latin(table):
    n = len(table)
    expected = list(range(n))
    assert all(sorted(row) == expected for row in table)
    assert all(sorted(row) == expected for row in zip(*table))


def check_e229(table):
    check_latin(table)
    n = len(table)
    assert all(table[table[y][table[y][x]]][y] == x
               for x in range(n) for y in range(n))


def check_e63(table):
    check_latin(table)
    n = len(table)
    assert all(table[y][table[x][table[x][y]]] == x
               for x in range(n) for y in range(n))
    assert all(table[x][x] == x for x in range(n))


def left_division(table):
    check_latin(table)
    return [[row.index(y) for y in range(len(table))] for row in table]


def reconstruct32():
    check_e229(C3_4)
    check_e63(E63_8)
    filler = left_division(E63_8)
    check_e229(filler)
    for x in range(8):
        expected = [y for y in range(8) if y % 4 != x % 4]
        assert sorted(y for y in PARTIAL8[x] if y is not None) == expected
        for y in range(8):
            assert PARTIAL8[x][y] == PARTIAL8[y][x]
            if x % 4 != y % 4:
                z = PARTIAL8[y][x]
                w = PARTIAL8[y][z]
                assert z is not None and w is not None
                assert PARTIAL8[w][y] == x

    def op(x, y):
        a, b = divmod(x, 4)
        c, d = divmod(y, 4)
        if a % 4 == c % 4:
            z = filler[4 * (a // 4) + b][4 * (c // 4) + d]
            return 4 * (a % 4 + 4 * (z // 4)) + z % 4
        return 4 * PARTIAL8[a][c] + C3_4[b][d]

    e229 = [[op(x, y) for y in range(32)] for x in range(32)]
    check_e229(e229)
    assert all(e229[x][x] == x for x in range(32))
    e63 = left_division(e229)
    check_e63(e63)
    return e63


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-lean", type=Path)
    args = parser.parse_args()
    table = reconstruct32()
    packed = sum(value << (5 * (32 * x + y))
                 for x, row in enumerate(table) for y, value in enumerate(row))
    literal = hex(packed)
    if args.check_lean:
        assert f"private def packedIdem32 : Nat := {literal}\n" in args.check_lean.read_text()
        print("Verified Bennett construction, all 1024 E63 instances, idempotence, and Lean certificate.")
    else:
        print(literal)


if __name__ == "__main__":
    main()

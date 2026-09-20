#!/usr/bin/env python3
"""Arithmetic regression for the analytic order-40, m=10, h=17 proof.

No magma search, SAT solver, or external dependency is used.  This checks
the ten allowed (sharp count, top excess) types, the small multiset
classification, and the auxiliary-support bounds in the linked note.
"""

from collections import Counter
from itertools import combinations_with_replacement
import sys


TYPES = tuple((j, e) for j in range(1, 5) for e in range(5 - j))


def remainder(j: int, e: int) -> int:
    return (j - 1) * (j - 2) + e * (j + e - 2)


def support_one_side(x: tuple[int, int], y: tuple[int, int]) -> int:
    j, e = x
    jy, _ = y
    inputs = min(5 - j, 1 + e + jy)
    return min(3 * inputs, 10 - (4 + e) + inputs)


def support(x: tuple[int, int], y: tuple[int, int]) -> int:
    return min(support_one_side(x, y), support_one_side(y, x))


def main() -> None:
    if not __debug__:
        sys.exit("Run without -O: this arithmetic regression uses assertions.")
    assert len(TYPES) == 10
    for j, e in TYPES:
        assert remainder(j, e) >= 0
        assert remainder(j, e) >= 2 * (j + e) - 5

    survivors = []
    for a in range(7, 11):
        b = 13 - a
        for profile in combinations_with_replacement(TYPES, b):
            if sum(j for j, _ in profile) != a:
                continue
            excess = sum(e for _, e in profile)
            if excess < 4:
                continue
            rem = sum(remainder(*x) for x in profile)
            top_pair_bound = 2 * a - 1 - 3 * excess - rem
            if top_pair_bound >= 0:
                survivors.append((a, b, profile, excess, rem, top_pair_bound))

    assert Counter(row[0] for row in survivors) == {7: 2, 8: 4}
    assert all(row[3] == 4 and row[5] <= 1 for row in survivors)
    for row in survivors:
        a, b, profile, excess, rem, upper = row
        print(f"a={a} b={b} E={excess} R={rem} N<={upper}: {profile}")
        if a == 8:
            assert any(j >= 2 and 4 - j - e > 0 for j, e in profile)

    low, medium = (1, 0), (1, 1)
    special_i, special_ii = (2, 1), (2, 0)
    for x in (low, medium, special_i):
        for y in (low, medium, special_i):
            assert support(x, y) <= 8
    assert support(low, low) <= 6
    assert support(low, medium) <= 6
    assert 13 * 8 - 5 * 2 == 94 < 100

    assert support(medium, medium) <= 8
    for x in (low, medium, special_ii):
        assert support(low, x) <= 6
    assert support(special_ii, medium) <= 6
    assert support(special_ii, special_ii) <= 9
    assert 13 * 8 + 1 - 5 * 2 == 95 < 100
    print("PASS: six arithmetic profiles; auxiliary support ceilings 94 and 95 < 100.")


if __name__ == "__main__":
    main()

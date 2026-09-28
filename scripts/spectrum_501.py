#!/usr/bin/env python3
"""Construct E501 models by taking square roots of abelian-group reflections.

The proof for all orders is in Spectrum/Equation501.lean. This executable
version checks the identity directly; it is not a source of Lean axioms.
"""

import argparse
import json


def involution_root(permutation):
    """Pair transpositions into four-cycles, leaving fixed points fixed."""
    n = len(permutation)
    assert all(permutation[permutation[i]] == i for i in range(n))
    pairs = [(i, permutation[i]) for i in range(n) if i < permutation[i]]
    assert len(pairs) % 2 == 0
    root = list(range(n))
    for (a, b), (c, d) in zip(pairs[::2], pairs[1::2]):
        root[a], root[c], root[b], root[d] = c, b, d, a
    assert all(root[root[i]] == permutation[i] for i in range(n))
    return root


def model(n):
    """Return and verify an E501 table of any positive order 0 or 1 mod 4."""
    if n <= 0 or n % 4 not in (0, 1):
        raise ValueError("The order must be positive and congruent to 0 or 1 modulo 4")
    if n % 4 == 1:
        reflections = [[(-x - y) % n for y in range(n)] for x in range(n)]
    else:
        m = n // 2
        # Encode (a, b) in Z/2 x Z/m as m*a + b.
        reflections = [
            [m * ((x // m + y // m) % 2) + (-(x % m) - (y % m)) % m
             for y in range(n)]
            for x in range(n)
        ]
    table = [involution_root(row) for row in reflections]
    assert all(table[y][table[y][table[x][table[x][y]]]] == x
               for x in range(n) for y in range(n))
    return table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=128,
                        help="verify every admissible positive order up to this bound")
    parser.add_argument("--order", type=int,
                        help="instead print one verified multiplication table as JSON")
    args = parser.parse_args()
    if args.order is not None:
        print(json.dumps(model(args.order)))
    else:
        count = 0
        for n in range(1, args.through + 1):
            if n % 4 in (0, 1):
                model(n)
                count += 1
        print(f"Verified {count} admissible orders through {args.through}.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Replay bounded extension tests for the OPEN fifty-operation E917 candidate.

No characterization is asserted. Each test checks an entire vector space of
additive offsets over one saved source's left-division table. NumPy is required.
The quotient is restricted to a known image; this does not exhaust finite magmas.
"""
import json
from functools import lru_cache
from pathlib import Path

import numpy as np

from check_parastrophe_e917_sandwich import F, G, H, rref, unit

ROOT = Path(__file__).resolve().parents[1]


def first(x, z, w):
    return F(z, w), H(x, z)


def second(x, z, w):
    return z, H(x, F(z, w))


def third(x, z, w):
    return G(w, z), H(x, z)


def candidate():
    k = ((second(0, 2, 3), (unit(0), first(0, 4, 5))), third(0, 6, 7))
    return 1, (k, (0, 1))


def check(source, prime, left, right):
    n = len(source)
    assert all(sorted(row) == list(range(n)) for row in source)
    assert all(source[y][source[source[y][y]][source[x][y]]] == x
               for x in range(n) for y in range(n))
    base = [[row.index(j) for j in range(n)] for row in source]
    zero = np.zeros(n*n, dtype=np.int64)

    @lru_cache(None)
    def coefficients(term):
        if isinstance(term, int):
            return tuple(int(i == term) for i in range(8))
        return tuple((left*x+right*y) % prime
                     for x, y in zip(coefficients(term[0]), coefficients(term[1])))

    assert coefficients(candidate()) == coefficients(0)

    @lru_cache(None)
    def value(term, x, y):
        if isinstance(term, int):
            return (x, y)[term], zero
        i, u = value(term[0], x, y)
        j, v = value(term[1], x, y)
        offset = (left*u+right*v) % prime
        offset = offset.copy()
        offset[i*n+j] = (offset[i*n+j]+1) % prime
        return base[i][j], offset

    identities = [(F(0, 1), F(0, 0)), (G(1, 0), G(0, 0))]
    identities += [(bridge(0, 1, 1), bridge(0, 0, 0))
                   for bridge in (first, second, third)]
    k = ((second(0, 0, 0), (unit(0), first(0, 0, 0))), third(0, 0, 0))
    identities.append(((1, (k, (0, 1))), 0))
    constraints = []
    for t, u in identities:
        assert coefficients(t) == coefficients(u)
        for x in range(n):
            for y in range(n):
                i, v = value(t, x, y)
                j, w = value(u, x, y)
                assert i == j
                constraints.append((v-w) % prime)
    matrix, pivots = rref(constraints, prime)
    for wanted in (unit(0), F(0, 0)):
        assert coefficients(wanted) == coefficients(0)
        for x in range(n):
            label, residual = value(wanted, x, x)
            assert label == x
            residual = residual.copy()
            for row, pivot in zip(matrix, pivots):
                residual = (residual-residual[pivot]*row) % prime
            assert not np.any(residual), (n, prime, left, right, x)


def main():
    data = ROOT / 'data/parastrophes'
    record = json.loads((data / 'e917_two_shifts_20261103.json').read_text())
    assert json.loads(json.dumps(candidate())) == record['candidate']['rhs']

    def size(t):
        return 0 if isinstance(t, int) else 1+size(t[0])+size(t[1])

    assert size(candidate()) == record['candidate']['operations'] == 50
    seeds = json.loads((data / 'repository_image_models_20261103.json').read_text())['sources']['917']['tables']
    count = 0
    for source in seeds:
        for prime in record['additive_extension_checks']['primes']:
            assert prime >= 2 and all(prime % d for d in range(2, int(prime**0.5)+1))
            for right in range(1, prime):
                left = -right**3 % prime
                qcoef = (left*left+left*right*(left+right)+right) % prime
                if right*left*(qcoef+right) % prime != 1 or (left+right*qcoef) % prime != 1:
                    continue
                check(source, prime, left, right)
                count += 1
    assert count == record['additive_extension_checks']['offset_spaces_checked'] == 340
    print(f'Checked {count} offset spaces; no counterexample. General converse remains open.')


if __name__ == '__main__':
    main()

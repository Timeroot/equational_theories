#!/usr/bin/env python3
"""Replay bounded E917 sandwich extension checks; these are not Lean proofs.

Requires NumPy. Each check covers a whole vector space of offset tables for
an operation (i,u)*(j,v)=(base[i][j], A*u+B*v+offset[i][j]). The quotient is
one of the ten saved division images. Parameter independence reduces the
four-variable candidate to the displayed two-variable identity, by the
general finite reduction in Equation917SandwichCandidate.lean.
"""

import json
from functools import lru_cache
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/parastrophes"


def core(x):
    return ((x, (x, x)), x)


def unit(x):
    return (x, core(x))


def H(x, y):
    return (core(x), (x, y))


def F(x, y):
    return (y, H(x, y))


def G(y, x):
    return H((y, x), y)


def rref(rows, prime):
    matrix = np.array(rows, dtype=np.int64) % prime
    rank, pivots = 0, []
    for column in range(matrix.shape[1]):
        nonzero = np.nonzero(matrix[rank:, column])[0]
        if not len(nonzero):
            continue
        pivot = rank + nonzero[0]
        matrix[[rank, pivot]] = matrix[[pivot, rank]]
        matrix[rank] = matrix[rank] * pow(int(matrix[rank, column]), -1, prime) % prime
        factors = matrix[:, column].copy()
        factors[rank] = 0
        matrix = (matrix - factors[:, None] * matrix[rank]) % prime
        pivots.append(column)
        rank += 1
        if rank == len(matrix):
            break
    return matrix[:rank], pivots


def check(source, prime, A, B):
    n = len(source)
    assert all(sorted(row) == list(range(n)) for row in source)
    assert all(source[y][source[source[y][y]][source[x][y]]] == x
               for x in range(n) for y in range(n))
    base = [[row.index(j) for j in range(n)] for row in source]
    zero = np.zeros(n*n, dtype=np.int64)

    @lru_cache(None)
    def value(term, x, y):
        if isinstance(term, int):
            return (x, y)[term], zero.copy()
        i, u = value(term[0], x, y)
        j, v = value(term[1], x, y)
        offset = (A*u+B*v) % prime
        offset[i*n+j] += 1
        return base[i][j], offset % prime

    common_a = F(0, 0)
    common_b = G(0, 0)
    # Substitution helpers keep the term's x argument explicit.
    a = lambda x: F(x, x)
    b = lambda x: G(x, x)
    normalized = (1, a(H(b(unit(0)), 1)))
    constraints = []
    for x in range(n):
        for y in range(n):
            constraints.append((value(F(0, 1), x, y)[1] - value(common_a, x, y)[1]) % prime)
            constraints.append((value(G(1, 0), x, y)[1] - value(common_b, x, y)[1]) % prime)
            label, offset = value(normalized, x, y)
            assert label == x
            constraints.append(offset)
    matrix, pivots = rref(constraints, prime)
    for term in [unit(0), common_a]:
        for x in range(n):
            label, residual = value(term, x, x)
            assert label == x
            residual = residual.copy()
            for row, pivot in zip(matrix, pivots):
                residual = (residual-residual[pivot]*row) % prime
            assert not np.any(residual), (n, prime, A, B, x)


def main():
    record = json.loads((DATA / "e917_sandwich_20261103.json").read_text())
    candidate = record["candidate"]
    tree = (1, F(H(G(2, unit(0)), 1), 3))
    assert candidate["lhs"] == 0
    assert candidate["rhs"] == json.loads(json.dumps(tree))

    def size(t):
        return 0 if isinstance(t, int) else 1+size(t[0])+size(t[1])

    assert size(tree) == candidate["operations"] == 782
    short = record["rejected_short_candidate"]
    table = short["table"]

    def evaluate(t, x, y):
        if isinstance(t, int):
            return (x, y)[t]
        return table[evaluate(t[0], x, y)][evaluate(t[1], x, y)]

    assert all(evaluate(short["rhs"], x, y) == x for x in range(3) for y in range(3))
    assert evaluate(unit(0), 0, 0) != 0
    sources = json.loads((DATA / "repository_image_models_20261103.json").read_text())["sources"]["917"]["tables"]
    expected = []
    for i, source in enumerate(sources):
        for prime in range(2, 44):
            if any(prime % d == 0 for d in range(2, int(prime**0.5)+1)):
                continue
            for B in range(1, prime):
                A = -B**3 % prime
                C = (A*A+A*B*(A+B)+B) % prime
                if (B*A*C+B*B*A) % prime != 1 or (A+B*C) % prime != 1:
                    continue
                check(source, prime, A, B)
                expected.append(dict(seed_index=i, seed_order=len(source), prime=prime, A=A, B=B))
    assert expected == record["additive_extension_checks"]["results"]
    assert len(expected) == record["additive_extension_checks"]["offset_spaces_checked"]
    print(f"Checked all {len(expected)} recorded offset spaces; no counterexample.")


if __name__ == "__main__":
    main()

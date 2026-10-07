#!/usr/bin/env python3
"""Reproduce two E125 counterexamples to proposed unary-map invariants.

Solve the linear central-extension equations over F_7. The unrestricted
cocycle basis gives a sparse 49-element example. Restricting to functions
linear under simultaneous translation gives the Heisenberg example.
Independent finite checks here are research validation; the Lean files
named in the output contain the proofs. Run with --output to save results.
"""

import argparse
from itertools import product
import json
from pathlib import Path

import numpy as np

P = 7
BASE_PAIRS = list(product(range(P), repeat=2))


def nullspace(matrix):
    """Deterministic reduced-row-echelon nullspace over F_7."""
    a = np.array(matrix, dtype=np.int64) % P
    rows, columns = a.shape
    rank, pivots = 0, []
    for column in range(columns):
        nonzero = np.flatnonzero(a[rank:, column])
        if not len(nonzero):
            continue
        pivot = rank + int(nonzero[0])
        a[[rank, pivot]] = a[[pivot, rank]]
        a[rank] = a[rank] * pow(int(a[rank, column]), -1, P) % P
        for row in range(rows):
            if row != rank and a[row, column]:
                a[row] = (a[row] - a[row, column] * a[rank]) % P
        pivots.append(column)
        rank += 1
        if rank == rows:
            break
    basis = []
    for column in range(columns):
        if column in pivots:
            continue
        vector = np.zeros(columns, dtype=np.int64)
        vector[column] = 1
        for row, pivot in enumerate(pivots):
            vector[pivot] = -a[row, column] % P
        assert np.all(np.array(matrix) @ vector % P == 0)
        basis.append(vector)
    return basis


def q(x, y):
    return (4 * x + 4 * y + 1) % P


def triangular_unary_group(table):
    """Certify the full unary group by seven-dimensional linear algebra."""
    def op(a, b):
        return q(a[0], b[0]), int((4 * a[1] + 4 * b[1] + table[a[0], b[0]]) % P)

    def coordinates(mapping):
        c = mapping((0, 0))[0]
        d = [mapping((x, 0))[1] for x in range(P)]
        for x, a in BASE_PAIRS:
            assert mapping((x, a)) == ((x + c) % P, (a + d[x]) % P)
        return c, d

    def compose(a, b):
        c, d = a
        e, f = b
        return (c + e) % P, [(f[x] + d[(x + e) % P]) % P for x in range(P)]

    def inverse(a):
        c, d = a
        return -c % P, [-d[(x - c) % P] % P for x in range(P)]

    square = coordinates(lambda a: op(a, a))
    cube = coordinates(lambda a: op(a, op(a, a)))
    inverse_fifth = (0, [0] * P)
    for _ in range(5):
        inverse_fifth = compose(inverse(square), inverse_fifth)
    zero_shift = compose(cube, inverse_fifth)
    assert square[0] == 1 and zero_shift[0] == 0
    shifts = [[zero_shift[1][(x + r) % P] for x in range(P)] for r in range(P)]
    assert not nullspace(shifts)
    return {
        "description": "Full triangular permutation group, C7 wreath C7",
        "square": square,
        "cube": cube,
        "cube_composed_square_inverse_fifth": zero_shift,
        "cyclic_shift_rank": P,
        "order": P ** (P + 1),
        "status": "Pen-and-paper proof and independent linear check; not separately Lean formalized",
    }


def search(features):
    rows = [
        (2 * features(y, x) + 4 * features(q(y, x), y)
         + features(y, q(q(y, x), y))) % P
        for x, y in BASE_PAIRS
    ]
    basis = nullspace(rows)
    for index, vector in enumerate(basis):
        table = np.array([
            [int(features(x, y) @ vector % P) for y in range(P)]
            for x in range(P)
        ])

        def op(a, b):
            return q(a[0], b[0]), int((4 * a[1] + 4 * b[1] + table[a[0], b[0]]) % P)

        def square(a):
            return op(a, a)

        def cube(a):
            return op(a, square(a))

        failures = [x for x in range(P) if square(cube((x, 0))) != cube(square((x, 0)))]
        if failures:
            for a, b in product(BASE_PAIRS, repeat=2):
                assert op(b, op(op(b, a), b)) == a
            return len(basis), index, vector, table, failures
    raise AssertionError("No counterexample found in this family")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    identity = np.eye(P * P, dtype=np.int64)
    dimension, index, _, table, failures = search(lambda x, y: identity[P * x + y])
    sparse = {
        "nullspace_dimension": dimension,
        "basis_index": index,
        "nonzero_cocycle_entries": [
            [x, y, int(table[x, y])] for x, y in BASE_PAIRS if table[x, y]
        ],
        "square_cube_defect_base_points": failures,
        "lean_source": "equational_theories/Definability/E125UnaryCountermodel.lean",
        "unary_term_group": triangular_unary_group(table),
    }
    assert sparse["nonzero_cocycle_entries"] == [[0, 2, 5], [2, 0, 5], [2, 2, 1]]
    monomials = list(product(range(2), range(P)))

    def features(x, y):
        return np.array([pow(x, i, P) * pow((y - x) % P, j, P) % P for i, j in monomials])

    dimension, index, vector, _, failures = search(features)
    u = [int(vector[j]) for j in range(P)]
    v = [int(vector[P + j]) for j in range(P)]
    assert u == [0, 4, 1, 6, 6, 5, 0]
    assert v == [0, 0, 5, 0, 3, 0, 1]

    def polynomial(coefficients, x):
        return sum(coefficient * pow(x, i, P) for i, coefficient in enumerate(coefficients)) % P

    def mul(a, b):
        return ((a[0] + b[0]) % P, (a[1] + b[1]) % P,
                (a[2] + b[2] + a[1] * b[0]) % P)

    def inv(a):
        return (-a[0] % P, -a[1] % P, (-a[2] + a[1] * a[0]) % P)

    def f(a):
        return ((4 * a[0] + 1) % P, (4 * a[1] + polynomial(v, a[0])) % P,
                (4 * a[2] + polynomial(u, a[0])) % P)

    for a in product(range(P), repeat=3):
        assert f(mul(f(inv(f(a))), f(a))) == a
    first, second = f((0, 0, 0)), f(f((0, 0, 0)))
    assert mul(first, second) != mul(second, first)
    heisenberg = {
        "nullspace_dimension": dimension,
        "basis_index": index,
        "cocycle_formula": "u(y-x) + x*v(y-x)",
        "u_coefficients_ascending": u,
        "v_coefficients_ascending": v,
        "square_cube_defect_base_points": failures,
        "group_order": P ** 3,
        "f_identity": first,
        "f_squared_identity": second,
        "products": [mul(first, second), mul(second, first)],
        "lean_source": "equational_theories/Definability/E125Heisenberg.lean",
    }
    result = {"field": P, "sparse_extension": sparse, "heisenberg_extension": heisenberg}
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()

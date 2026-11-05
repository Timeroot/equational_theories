#!/usr/bin/env python3
"""Independently replay the E477/E680 singular affine constructions.

Lean proves the all-primes result and equation transfer. This checker audits
the saved data using exact coefficient vectors and small literal tables.
"""
import itertools
import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def check(record):
    q, a, b = (record[k] for k in ("base", "A", "B"))
    n = len(q)
    number = record["equation"]
    assert number in (477, 680) and n == 3
    assert all(len(row) == n for matrix in (q, a, b) for row in matrix)
    assert all(sorted(row) == list(range(n)) for row in q)
    assert all(value in (-2, -1, 1, 2) for row in b for value in row)

    # A coordinate is a linear form in u,v, represented by its two coefficients.
    def op(x, y):
        i, u = x
        j, v = y
        return q[i][j], tuple(a[i][j] * s + b[i][j] * t for s, t in zip(u, v))

    def core(x):
        return op(x, op(x, x))

    for i, j in itertools.product(range(n), repeat=2):
        x, y = (i, (1, 0)), (j, (0, 1))
        assert core(x) == (i, (2, 0))
        assert op(x, op(y, x)) == core(y)
        if number == 477:
            assert op(x, op(x, core(x))) == x
        else:
            assert op(x, core(x)) == op(core(x), x)

    def table(p):
        return [[p * q[x // p][y // p]
                 + (a[x // p][y // p] * (x % p) + b[x // p][y // p] * (y % p)) % p
                 for y in range(n * p)] for x in range(n * p)]

    bad = table(2)
    row = record["collision"]["row"]
    inputs = record["collision"]["inputs"]
    encode = lambda x: 2 * x[0] + x[1]
    assert inputs[0] != inputs[1]
    assert bad[encode(row)][encode(inputs[0])] == bad[encode(row)][encode(inputs[1])]
    equation = load_equations()[number - 1]
    for p in (3, 5, 7):
        d = table(p)
        assert all(sorted(row) == list(range(n * p)) for row in d)
        source = [[row.index(j) for j in range(n * p)] for row in d]
        assert satisfies(*equation, sum(source, []), n * p)
    print(f"E{number}: integer identities, six-element collision, and prime reductions checked.")


if __name__ == "__main__":
    path = Path(__file__).resolve().parents[1] / "data/parastrophes/crossed_singular_images_20261105.json"
    for record in json.loads(path.read_text())["records"]:
        check(record)

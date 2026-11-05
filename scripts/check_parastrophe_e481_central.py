#!/usr/bin/env python3
"""Reconstruct the new finite cross-inverse loop and check its saved refutation.

This is research validation, not an exported Lean result. The large division
magma is evaluated through two coordinates; its multiplication table is never
materialized. The cross-inverse loop, its automorphism, and its bijectivity
are checked before applying the mathematical Cartesian-square construction.
"""
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    r = json.loads((ROOT / "data/parastrophes/e481_central_extension_20261104.json").read_text())
    p = r["prime"]
    points = list(itertools.product(range(p), repeat=2))
    index = {x: i for i, x in enumerate(points)}

    def correction(x, y):
        return (0 if x == 0 or y == 0 else x if (x + y) % p == 0
                else (x - y) * pow(3, -1, p) % p)

    def base_op(x, y):
        return ((x[0] + y[0]) % p,
                (x[1] + y[1] + correction(x[0], y[0])) % p)

    n = len(points)
    base = [[index[base_op(x, y)] for y in points] for x in points]
    j = [index[(-a % p, (-b - a) % p)] for a, b in points]
    c = r["offset"]
    assert len(c) == n and all(len(row) == n for row in c)
    assert all(0 <= x < p for row in c for x in row)
    for x in range(n):
        assert c[0][x] == c[x][0] == 0
        for y in range(n):
            assert (c[x][y] + c[base[x][y]][j[x]] - c[x][j[x]]) % p == 0

    def lift(x, y):
        a, u = divmod(x, p)
        b, v = divmod(y, p)
        return p * base[a][b] + (u + v + c[a][b]) % p

    size = n * p
    table = [[lift(x, y) for y in range(size)] for x in range(size)]
    inv = [row.index(0) for row in table]
    for x in range(size):
        assert table[0][x] == table[x][0] == x
        assert sorted(table[x]) == sorted(table[y][x] for y in range(size)) == list(range(size))
        for y in range(size):
            assert table[table[x][y]][inv[x]] == y
            assert table[x][table[y][inv[x]]] == y
            assert inv[table[x][y]] == table[inv[x]][inv[y]]
    assert sorted(inv) == list(range(size))
    cycle = r["loop_inverse_cycle"]
    assert len(set(cycle)) == len(cycle) == 50
    assert all(inv[x] == cycle[(k + 1) % len(cycle)] for k, x in enumerate(cycle))

    def division(a, b):
        return (table[a[0]][b[1]], table[a[1]][inv[b[0]]])

    def value(t):
        if t == "e":
            return (0, 0)
        if t == "x":
            return tuple(r["input"])
        return division(value(t[0]), value(t[1]))

    result = value(r["rejected_eight_operation_term"])
    assert result == tuple(r["output"]) != tuple(r["input"])
    print(f"Checked the {size}-element loop, its inverse 50-cycle, and the refutation "
          f"in its {size * size}-element division magma: {r['input']} -> {list(result)}.")


if __name__ == "__main__":
    main()

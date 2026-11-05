#!/usr/bin/env python3
"""Replay the compact E917 comparison counterexample, independently of Lean.

Lean checks its fibre coordinates symbolically. This inexpensive independent
replay also evaluates the twelve-operation identity on all 25^3 assignments.
The refutation concerns one proposed identity, not every image characterization.
"""
import json
from itertools import product
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / "data/parastrophes/e917_left_comparison_20261104.json").read_text())
    source, base = data["base_source"], data["base_division"]
    p, a, b, offset = (data[k] for k in ("p", "A", "B", "offset"))
    n = len(base)
    for x, y in product(range(n), repeat=2):
        assert source[x][base[x][y]] == y
        assert base[x][source[x][y]] == y
        assert source[y][source[source[y][y]][source[x][y]]] == x
    size = n * p
    table = [[p * base[x // p][y // p]
              + (a * (x % p) + b * (y % p) + offset[x // p][y // p]) % p
              for y in range(size)] for x in range(size)]
    points = list(range(size))
    assert all(sorted(row) == points for row in table)
    assert all(sorted(table[x][y] for x in points) == points for y in points)
    q = [table[table[x][table[x][x]]][x] for x in points]
    unit = [table[x][q[x]] for x in points]
    for x in points:
        assert unit[x] == p * (x // p) + (x % p + 1) % p
    for x, y, z in product(points, repeat=3):
        assert table[table[unit[z]][y]][table[q[x]][table[x][table[z][y]]]] == x
    assert unit[0] != 0  # Every actual image satisfies U(x)=x.
    print("PASS: 25-element quasigroup satisfies the candidate and fails the image basis.")


if __name__ == "__main__":
    main()

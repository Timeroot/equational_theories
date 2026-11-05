#!/usr/bin/env python3
"""Exact symbolic replay of the three-block E1518 construction (research).

This is not a Lean certificate. SymPy computes in Z[1/2,i]/(i²+1),
which maps to every commutative ring with i²=-1 and 2 invertible.
"""
import json
from pathlib import Path

import sympy as sp


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / "data/parastrophes/e1518_three_block_affine_20261104.json").read_text())
    i, h = sp.symbols("i h")
    a = [[sp.sympify(v, locals={"i": i, "h": h}) for v in row] for row in data["A"]]
    b = [[sp.sympify(v, locals={"i": i, "h": h}) for v in row] for row in data["B"]]

    def zero(value):
        polynomial = sp.Poly(sp.expand(value.subs(h, sp.Rational(1, 2))), i)
        assert all(c.q & (c.q - 1) == 0 for c in polynomial.all_coeffs())
        assert sp.rem(polynomial, sp.Poly(i**2 + 1, i)).is_zero

    for y in range(3):
        for x in range(3):
            cy, cx = (y + 1) % 3, (x + 1) % 3
            out = (x + 2) % 3
            zero(a[cy][out] * (a[y][y] + b[y][y]) +
                 b[cy][out] * b[x][cx] * a[y][x])
            zero(b[cy][out] * (a[x][cx] + b[x][cx] * b[y][x]) - 1)
    for phase in range(3):
        zero(a[phase][phase] + b[phase][phase] - (i if phase == 2 else 1))

    seed = json.loads((root / "data/parastrophes/e1518_square_cycles_20261103.json").read_text())["seed"]["table"]
    coordinates = {13: (0, 0), 14: (1, 0), 12: (2, 0)}
    coordinates.update({k: (k % 3, pow(3, k // 3, 5)) for k in range(12)})
    aa = [[int(v.subs({i: 3, h: 3})) % 5 for v in row] for row in a]
    bb = [[int(v.subs({i: 3, h: 3})) % 5 for v in row] for row in b]
    for x in range(15):
        for y in range(15):
            p, u = coordinates[x]
            q, v = coordinates[y]
            assert coordinates[seed[x][y]] == ((q + 1) % 3, (aa[p][q] * u + bb[p][q] * v) % 5)
    print("18 law coefficients, 3 square coefficients and all 225 seed entries checked exactly.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Replay the six scalar witnesses for ALL E917 outer-unit exponents.

The Lean theorem supplies the symbolic evaluation and periodicity arguments.
This independent arithmetic replay checks the saved coefficients and the cover
of the twelve residue classes. It uses neither a solver nor magma tables.
"""
import json
from pathlib import Path


def main():
    path = Path(__file__).resolve().parents[1] / (
        "data/parastrophes/e917_outer_powers_20261104.json")
    data = json.loads(path.read_text())
    covered = set()
    for seed in data["counterexamples"]:
        p, a, b = (seed[key] for key in ("p", "a", "b"))
        assert 0 < p <= 197
        assert a * seed["a_inverse"] % p == 1
        assert b * seed["b_inverse"] % p == 1
        q = (a*a + a*a*b + a*b*b + b) % p
        u = (a + b*q) % p
        assert q == seed["q_coefficient"]
        assert u == seed["u_coefficient"] and u != 1
        assert pow(u, 12, p) == 1
        # Coefficients of x and y in D(U^k(y), D(q(x), D(x,y))).
        assert a*b*(q+b) % p == 1
        residues = seed["residues_mod_12"]
        assert residues and len(residues) == len(set(residues))
        assert all(0 <= k < 12 and (a*pow(u, k, p)+b**3) % p == 0
                   for k in residues)
        covered.update(residues)
    assert covered == set(range(12))
    print("Six quasigroups verified; all twelve residue classes covered.")


if __name__ == "__main__":
    main()

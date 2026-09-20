#!/usr/bin/env python3
"""Explore affine-model counts on remaining TS/fin cells; never add proof facts."""

import argparse
from functools import lru_cache
import json
from pathlib import Path

import numpy as np

from spectrum_generate import load_equations, variables

ROOT = Path(__file__).resolve().parents[1]


def affine_parameters(equation, modulus):
    """Return (a,b,d) for admissible linear parts, with the shift constraint d*c=0."""
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    a = np.repeat(np.arange(modulus, dtype=np.int64), modulus)
    b = np.tile(np.arange(modulus, dtype=np.int64), modulus)
    lhs, rhs = equation

    @lru_cache(None)
    def coeff(term, var):
        if isinstance(term, str):
            return int(term == var)
        return (
            a * coeff(term[0], var) + b * coeff(term[1], var) + (var is None)
        ) % modulus

    good = np.ones(modulus * modulus, dtype=bool)
    for var in variables(lhs) | variables(rhs):
        good &= coeff(lhs, var) == coeff(rhs, var)
    dc = (coeff(lhs, None) - coeff(rhs, None)) % modulus
    return a[good], b[good], np.broadcast_to(dc, a.shape)[good]


def affine_model_count(equation, modulus):
    """Count admissible shifts with gcd(d,n), without enumerating triples."""
    _, _, dc = affine_parameters(equation, modulus)
    return int(np.gcd(dc, modulus).sum())


def affine_models(equation, modulus):
    """List all distinct coefficient triples in lexicographic order."""
    a, b, dc = affine_parameters(equation, modulus)
    steps = modulus // np.gcd(dc, modulus)
    return [
        (int(x), int(y), c)
        for x, y, step in zip(a, b, steps)
        for c in range(0, modulus, int(step))
    ]


def find_obstructions(equations, pairs, min_modulus, max_modulus):
    remaining = set(map(tuple, pairs))
    for modulus in range(min_modulus, max_modulus + 1):
        counts = {
            law: affine_model_count(equations[law - 1], modulus)
            for law in {v for pair in remaining for v in pair}
        }
        for source, target in sorted(remaining.copy()):
            if counts[source] > counts[target]:
                yield dict(
                    source=source,
                    target=target,
                    modulus=modulus,
                    source_count=counts[source],
                    target_count=counts[target],
                )
                remaining.remove((source, target))
        if not remaining:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pair", type=int, nargs=2, action="append")
    parser.add_argument("--min-modulus", type=int, default=2)
    parser.add_argument("--max-modulus", type=int, default=50)
    args = parser.parse_args()
    if not 2 <= args.min_modulus <= args.max_modulus <= 1000:
        parser.error("require 2 <= min-modulus <= max-modulus <= 1000")
    if args.pair and any(not 1 <= i <= 4694 for pair in args.pair for i in pair):
        parser.error("equation numbers must lie in 1..4694")
    snapshot = json.loads((ROOT / "docs/definability_open/snapshot.json").read_text())
    board = snapshot["boards"]["termStructural/fin"]
    pairs = args.pair or [
        (int(s), t)
        for s, profiles in board["open_rows"].items()
        for ts in profiles.values()
        for t in ts
    ]
    found = 0
    for entry in find_obstructions(
        load_equations(), pairs, args.min_modulus, args.max_modulus
    ):
        print(json.dumps(entry), flush=True)
        found += 1
    print(f"DONE: {found} candidate inequalities; no proof facts written.")


if __name__ == "__main__":
    main()

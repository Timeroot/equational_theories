#!/usr/bin/env python3
"""Find laws satisfied by the integral matrix families used for image obstructions.

Coefficients are computed exactly in Z[t]/f(t) for a supplied monic polynomial.
The default families use f(t)=t^d-t-1, for d=2 or 3. This is research support;
the law, division and no-characterization proofs live in Lean.
Pass equation numbers to restrict the scan, or omit them to scan the catalogue.
"""

import argparse
import json
from pathlib import Path

from spectrum_generate import load_equations


FAMILIES = {
    "plastic115": ((0, 0, -1), (0, 1, 0)),
    "plastic222": ((1, 0, -1), (0, 0, 1)),
    "golden124": ((1, -1), (0, 1)),
    "plastic667": ((-1, -1, 0), (0, 1, 0)),
    "plastic271": ((0, -1, 0), (1, 1, 0)),
    "plastic1119": ((1, -1, 0), (0, 1, 0)),
    "golden679": ((-2, 0), (0, 1)),
}


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mul(a, b, companion=None):
    d = len(a)
    companion = companion if companion is not None else (1, 1) + (0,) * (d - 2)
    product = [0] * (2 * d - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            product[i + j] += x * y
    for i in range(2 * d - 2, d - 1, -1):
        for j, c in enumerate(companion):
            product[i - d + j] += c * product[i]
    return tuple(product[:d])


def coefficients(term, a, b, companion=None):
    d = len(a)
    zero = (0,) * d
    if isinstance(term, str):
        return {term: (1,) + (0,) * (d - 1)}
    left = coefficients(term[0], a, b, companion)
    right = coefficients(term[1], a, b, companion)
    return {
        var: add(mul(a, left.get(var, zero), companion),
                 mul(b, right.get(var, zero), companion))
        for var in left.keys() | right.keys()
    }


def holds(equation, a, b, companion=None):
    left, right = (coefficients(term, a, b, companion) for term in equation)
    zero = (0,) * len(a)
    return all(left.get(var, zero) == right.get(var, zero) for var in left.keys() | right.keys())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("equations", nargs="*", type=int)
    parser.add_argument("--families-data", type=Path,
                        help="JSON companion families, including division coefficients p and q")
    args = parser.parse_args()
    equations = load_equations()
    candidates = args.equations or range(1, len(equations) + 1)
    if any(n < 1 or n > len(equations) for n in candidates):
        parser.error(f"Equation numbers must lie between 1 and {len(equations)}.")
    families = [(name, a, b, None) for name, (a, b) in FAMILIES.items()]
    if args.families_data:
        families = []
        for family in json.loads(args.families_data.read_text())["families"]:
            a, b, p, q, c = (tuple(family[k]) for k in ["a", "b", "p", "q", "companion"])
            if len({len(a), len(b), len(p), len(q), len(c)}) != 1 or len(c) < 2:
                parser.error("Family coefficient vectors must have the same dimension, at least two.")
            one = (1,) + (0,) * (len(c) - 1)
            zero = (0,) * len(c)
            if mul(b, q, c) != one or add(a, mul(b, p, c)) != zero:
                parser.error(f"Invalid division coefficients for E{family['source']}.")
            for n in family["laws"]:
                if not holds(equations[n - 1], a, b, c):
                    parser.error(f"Family E{family['source']} does not satisfy E{n}.")
            families.append((f"companion{family['source']}", a, b, c))
    result = {name: [n for n in candidates if holds(equations[n - 1], a, b, c)]
              for name, a, b, c in families}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

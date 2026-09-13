#!/usr/bin/env python3
"""Find finite witnesses requested by the note; Lean checks the output separately.

Reuses existing tables, tries cyclic linear models, and then bounded Z3 search.
Unsat/timeouts do not assert exclusions. --write updates the witness cache only.
"""
import argparse
import ast
import json
from itertools import product
from pathlib import Path
from spectrum_generate import ROOT, load_equations, satisfies, variables, equal_coefficients
from spectrum_note import FINITE


def field_table(lhs, rhs, n):
    fields = {4: (2, [1, 1]), 8: (2, [1, 1, 0]), 9: (3, [1, 0]), 16: (2, [1, 1, 0, 0])}
    if n not in fields:
        return None
    p, modulus = fields[n]
    d = len(modulus)
    digits = [[(x // (p ** k)) % p for k in range(d)] for x in range(n)]

    def encode(xs):
        return sum((x % p) * p ** k for k, x in enumerate(xs))

    def add(x, y):
        return encode([a + b for a, b in zip(digits[x], digits[y])])

    def mul(x, y):
        cs = [0] * (2 * d - 1)
        for j in range(d):
            for k in range(d):
                cs[j + k] += digits[x][j] * digits[y][k]
        for k in range(2 * d - 2, d - 1, -1):
            for j in range(d):
                cs[k - d + j] -= cs[k] * modulus[j]
        return encode(cs[:d])

    def coeff(term, a, b):
        if isinstance(term, str):
            return {term: 1}
        u, v = coeff(term[0], a, b), coeff(term[1], a, b)
        return {x: add(mul(a, u.get(x, 0)), mul(b, v.get(x, 0))) for x in u.keys() | v.keys()}

    for a, b in product(range(n), repeat=2):
        u, v = coeff(lhs, a, b), coeff(rhs, a, b)
        if all(u.get(x, 0) == v.get(x, 0) for x in u.keys() | v.keys()):
            return [add(mul(a, x), mul(b, y)) for x, y in product(range(n), repeat=2)]
    return None


def solve(lhs, rhs, n, timeout):
    import z3
    op = z3.Function("op", z3.IntSort(), z3.IntSort(), z3.IntSort())
    solver = z3.Solver()
    solver.set(timeout=timeout)
    for x, y in product(range(n), repeat=2):
        solver.add(op(x, y) >= 0, op(x, y) < n)
    vs = sorted(variables(lhs) | variables(rhs))

    def ev(term, vals):
        return vals[term] if isinstance(term, str) else op(ev(term[0], vals), ev(term[1], vals))

    for vals in product(range(n), repeat=len(vs)):
        assignment = dict(zip(vs, vals))
        solver.add(ev(lhs, assignment) == ev(rhs, assignment))
    if solver.check() != z3.sat:
        return None
    model = solver.model()
    return [model.eval(op(x, y)).as_long() for x, y in product(range(n), repeat=2)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=2000)
    args = parser.parse_args()
    path = ROOT / "data/spectrum_witnesses.json"
    cache = json.loads(path.read_text()) if path.exists() else {}
    equations = load_equations()
    tables = {}
    for filename in ["smallest_magma_examples.txt", "small_magma_examples.txt"]:
        for line in (ROOT / "data" / filename).read_text().splitlines():
            _, raw = line.split(" ", 1)
            table = ast.literal_eval(raw)
            flat = tuple(x for row in table for x in row)
            tables.setdefault(len(table), set()).add(flat)
    for i, sizes in FINITE.items():
        for n in sizes:
            key = f"{i}:{n}"
            lhs, rhs = equations[i - 1]
            if key in cache:
                assert satisfies(lhs, rhs, cache[key], n)
                continue
            ab = next(((a, b) for a, b in product(range(n), repeat=2)
                       if equal_coefficients(lhs, rhs, a, b, n)), None)
            table = ([(ab[0] * x + ab[1] * y) % n for x, y in product(range(n), repeat=2)]
                     if ab else next((list(t) for t in sorted(tables.get(n, []))
                                      if satisfies(lhs, rhs, t, n)), None))
            if table is None:
                table = field_table(lhs, rhs, n)
            if table is None:
                for d in range(2, n):
                    if n % d or f"{i}:{d}" not in cache or f"{i}:{n // d}" not in cache:
                        continue
                    e = n // d
                    u, v = cache[f"{i}:{d}"], cache[f"{i}:{e}"]
                    table = [e * u[d * (x // e) + y // e] + v[e * (x % e) + y % e]
                             for x, y in product(range(n), repeat=2)]
                    break
            if table is None:
                table = solve(lhs, rhs, n, args.timeout_ms)
            if table is not None:
                assert satisfies(lhs, rhs, table, n)
                cache[key] = table
                tables.setdefault(n, set()).add(tuple(table))
                print(key, "witness", flush=True)
            else:
                print(key, "not found (no exclusion asserted)", flush=True)
    if args.write:
        path.write_text(json.dumps(cache, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()

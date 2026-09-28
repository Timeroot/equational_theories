#!/usr/bin/env python3
"""Exploratory constructions for every remaining spectrum family.

Outputs are research evidence, not Lean certificates. A solver timeout never
excludes an order. Every positive table is checked directly against equations.txt.
"""
import argparse
from functools import cache
from itertools import product
import json
from math import gcd
from pathlib import Path
import time

import sympy as sp

from spectrum_generate import ROOT, coefficients, load_equations, satisfies, variables

FAMILIES = [63, 467, 667, 670, 677, 704, 883, 907, 1076, 1083, 1110,
            1279, 1286, 1313, 1483, 1486, 1516]


class Field:
    """Polynomial-basis finite field, with low coefficients first."""
    def __init__(self, p, modulus):
        self.p, self.modulus = p, modulus
        self.d = len(modulus) - 1
        self.q = p ** self.d
        self.digits = [[n // p**i % p for i in range(self.d)] for n in range(self.q)]

    def encode(self, values):
        return sum((x % self.p) * self.p**i for i, x in enumerate(values))

    @cache
    def add(self, x, y):
        return self.encode([a + b for a, b in zip(self.digits[x], self.digits[y])])

    def neg(self, x):
        return self.encode([-a for a in self.digits[x]])

    @cache
    def mul(self, x, y):
        cs = [0] * (2 * self.d - 1)
        for i, a in enumerate(self.digits[x]):
            for j, b in enumerate(self.digits[y]):
                cs[i + j] += a * b
        for k in range(2 * self.d - 2, self.d - 1, -1):
            for j in range(self.d):
                cs[k - self.d + j] -= cs[k] * self.modulus[j]
        return self.encode(cs[:self.d])

    def coeff(self, term, a, b):
        if isinstance(term, str):
            return {term: 1}
        u, v = (self.coeff(t, a, b) for t in term)
        return {x: self.add(self.mul(a, u.get(x, 0)), self.mul(b, v.get(x, 0)))
                for x in u.keys() | v.keys()}

    def table(self, a, b):
        return [self.add(self.mul(a, x), self.mul(b, y))
                for x, y in product(range(self.q), repeat=2)]


def fields(bound):
    t = sp.Symbol("t")
    for p in sp.primerange(2, bound + 1):
        d = 1
        while p**d <= bound:
            if d == 1:
                modulus = [0, 1]
            else:
                modulus = next(list(c) + [1] for c in product(range(p), repeat=d)
                               if c[0] and sp.Poly(t**d + sum(c[i]*t**i for i in range(d)),
                                                  t, modulus=p).is_irreducible)
            yield Field(int(p), modulus)
            d += 1


def subterms(term):
    if isinstance(term, str):
        return []
    return [term] + subterms(term[0]) + subterms(term[1])


def field_survey(bound):
    eqs = load_equations()
    a, b = sp.symbols("a b")
    report = {str(i): {"models": {}, "idempotent_models": {}, "strong_models": {}}
              for i in FAMILIES}
    for i in FAMILIES:
        lhs, rhs = eqs[i-1]
        u, v = coefficients(lhs, a, b), coefficients(rhs, a, b)
        polys = [sp.expand(v.get(x, 0) - u.get(x, 0)) for x in sorted(u.keys() | v.keys())]
        report[str(i)]["coefficient_equations"] = list(map(str, polys))
        report[str(i)]["idempotent_polynomial"] = str(sp.factor(sp.gcd_list(
            [p.subs(a, 1-b) for p in polys])))
    for f in fields(bound):
        for i in FAMILIES:
            lhs, rhs = eqs[i-1]
            entry = report[str(i)]
            for a, b in product(range(f.q), repeat=2):
                u, v = f.coeff(lhs, a, b), f.coeff(rhs, a, b)
                if any(u.get(x, 0) != v.get(x, 0) for x in u.keys() | v.keys()):
                    continue
                record = {"p": f.p, "modulus": f.modulus, "a": a, "b": b}
                categories = ["models"]
                if f.add(a, b) == 1:
                    categories.append("idempotent_models")
                    # On distinct inputs x,y, no multiplication node may have
                    # equal arguments. In an idempotent affine field model this
                    # is equivalent to unequal x-coefficients at that node.
                    if all(f.coeff(s[0], a, b).get("x", 0) !=
                           f.coeff(s[1], a, b).get("x", 0)
                           for s in subterms(lhs) + subterms(rhs)):
                        categories.append("strong_models")
                for category in categories:
                    if str(f.q) not in entry[category]:
                        assert satisfies(lhs, rhs, f.table(a, b), f.q)
                        entry[category][str(f.q)] = record
        print("field", f.q, "checked", flush=True)
    for entry in report.values():
        orders = list(map(int, entry["idempotent_models"]))
        entry["design_alpha"] = gcd(*(n-1 for n in orders)) if orders else None
        entry["design_beta"] = gcd(*(n*(n-1) for n in orders)) if orders else None
        done = {1, *map(int, entry["models"])}
        recipes = {}
        for n in range(2, 1228):
            if n not in done:
                for d in range(2, int(n**0.5) + 1):
                    if n % d == 0 and d in done and n // d in done:
                        done.add(n)
                        recipes[str(n)] = [d, n // d]
                        break
        entry["product_closure_below_1228"] = sorted(done)
        entry["product_recipes"] = recipes
    return {"status": "COMPUTER_CHECKED_NOT_LEAN", "field_bound": bound, "families": report}


def finite_search(law, n, seconds, restriction="none"):
    import z3
    if not 1 <= law <= 4694 or n < 2 or seconds <= 0:
        raise ValueError("Require a law in 1..4694, order at least two, and a positive timeout")
    lhs, rhs = load_equations()[law-1]
    context = z3.Context()
    carrier, elements = z3.EnumSort("Carrier", [f"e{i}" for i in range(n)], ctx=context)
    op = z3.Function("op", carrier, carrier, carrier)
    solver = z3.Solver(ctx=context)
    solver.set(timeout=int(seconds * 1000))
    vs = sorted(variables(lhs) | variables(rhs))
    def ev(term, vals):
        return vals[term] if isinstance(term, str) else op(ev(term[0], vals), ev(term[1], vals))
    for values in product(elements, repeat=len(vs)):
        vals = dict(zip(vs, values))
        solver.add(ev(lhs, vals) == ev(rhs, vals))
    solver.add(z3.Or(op(elements[0], elements[0]) == elements[0],
                     op(elements[0], elements[0]) == elements[1]))
    if restriction == "idempotent":
        solver.add([op(x, x) == x for x in elements])
    if restriction == "left_identity":
        solver.add([op(elements[0], x) == x for x in elements])
    start = time.monotonic()
    status = solver.check()
    result = {"law": law, "order": n, "restriction": restriction,
              "status": str(status), "seconds": round(time.monotonic()-start, 3),
              "timeout_seconds": seconds, "lean_proof": False}
    if status == z3.sat:
        model = solver.model()
        indices = {str(e): i for i, e in enumerate(elements)}
        table = [indices[str(model.eval(op(x, y), model_completion=True))]
                 for x, y in product(elements, repeat=2)]
        assert satisfies(lhs, rhs, table, n)
        result["table"] = table
    if status == z3.unknown:
        result["reason"] = solver.reason_unknown()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--field-bound", type=int, default=81)
    parser.add_argument("--search", nargs=2, type=int, metavar=("LAW", "ORDER"))
    parser.add_argument("--seconds", type=float, default=15)
    parser.add_argument("--restriction", choices=["none", "idempotent", "left_identity"], default="none")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.search:
        result = finite_search(*args.search, args.seconds, args.restriction)
    else:
        result = field_survey(args.field_bound)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Saved", args.output, flush=True)


if __name__ == "__main__":
    main()

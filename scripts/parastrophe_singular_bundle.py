#!/usr/bin/env python3
"""Search for singular division-image families over saved finite source models.

Division on the parts is the inverse of each source row. Its fibre operation
is A_ij*u+B_ij*v, where A is zero or a signed nonnegative power of T, and B is
a signed nonnegative power of T. The inverse source coefficients are -A/B
and 1/B. Expanding a source law yields signed Laurent monomials; cancellation
is encoded by pairing opposite signs at equal exponents. Some B exponent
must be positive, making reduction at T=0 singular.

This bounded search proves no negative claims. Found data require independent
verification and Lean proofs before catalogue registration. The E477/E680
families use T=2 and are verified in CrossedSingularImages.lean.
"""
import argparse
import itertools
import json
import time
from pathlib import Path

import z3
from spectrum_generate import load_equations, satisfies, variables


def solve(source, equation, seconds):
    n = len(source)
    solver = z3.Solver()
    solver.set(timeout=int(seconds * 1000))

    def matrix(prefix, constructor):
        return [[constructor(f"{prefix}_{i}_{j}") for j in range(n)] for i in range(n)]

    ae, be = matrix("ae", z3.Int), matrix("be", z3.Int)
    az, an, bn = (matrix(prefix, z3.Bool) for prefix in ("az", "an", "bn"))
    cells = list(itertools.product(range(n), repeat=2))
    for i, j in cells:
        solver.add(ae[i][j] >= 0, ae[i][j] <= 8, be[i][j] >= 0, be[i][j] <= 3)
    solver.add(z3.Or([be[i][j] > 0 for i, j in cells]))
    false, true = z3.BoolVal(False), z3.BoolVal(True)

    # A monomial is (integer exponent, negative sign, vanishing flag).
    def multiply(a, b):
        return a[0] + b[0], z3.Xor(a[1], b[1]), z3.Or(a[2], b[2])

    def zero(terms):
        if not terms:
            return true
        exponent, sign, vanishes = terms[0]
        rest = terms[1:]
        alternatives = [z3.And(vanishes, zero(rest))]
        for k, other in enumerate(rest):
            alternatives.append(z3.And(
                z3.Not(vanishes), z3.Not(other[2]), exponent == other[0], sign != other[1],
                zero(rest[:k] + rest[k + 1:]),
            ))
        return z3.Or(alternatives)

    names = sorted(variables(equation[0]) | variables(equation[1]))
    for parts in itertools.product(range(n), repeat=len(names)):
        assignment = dict(zip(names, parts))

        def evaluate(term):
            if isinstance(term, str):
                return assignment[term], {term: [(0, false, false)]}
            i, a = evaluate(term[0])
            j, b = evaluate(term[1])
            k = source[i][j]
            left = ae[i][k] - be[i][k], z3.Not(z3.Xor(an[i][k], bn[i][k])), az[i][k]
            right = -be[i][k], bn[i][k], false
            return k, {
                v: [multiply(left, c) for c in a.get(v, [])]
                   + [multiply(right, c) for c in b.get(v, [])]
                for v in names
            }

        i, a = evaluate(equation[0])
        j, b = evaluate(equation[1])
        assert i == j
        for v in names:
            solver.add(zero(a.get(v, []) + [(e, z3.Not(s), z) for e, s, z in b.get(v, [])]))

    start = time.monotonic()
    answer = solver.check()
    result = {"n": n, "status": str(answer), "seconds": time.monotonic() - start}
    if answer == z3.sat:
        model = solver.model()

        def value(expression):
            return model.eval(expression, model_completion=True)

        a = [[0 if z3.is_true(value(az[i][j])) else
              (-1 if z3.is_true(value(an[i][j])) else 1) * 2 ** value(ae[i][j]).as_long()
              for j in range(n)] for i in range(n)]
        b = [[(-1 if z3.is_true(value(bn[i][j])) else 1) * 2 ** value(be[i][j]).as_long()
              for j in range(n)] for i in range(n)]
        result.update(source=source, base=[[row.index(j) for j in range(n)] for row in source],
                      A=a, B=b, parameter=2)
    return result


def saved_sources(number, maximum):
    root = Path(__file__).resolve().parents[1]
    unique = {}
    for path in sorted((root / "data/parastrophes").glob("*.json")):
        data = json.loads(path.read_text())
        sources = data.get("sources", {}) if isinstance(data, dict) else {}
        entry = sources.get(str(number), {}) if isinstance(sources, dict) else {}
        if not isinstance(entry, dict):
            continue
        for table in entry.get("tables", []):
            n = len(table)
            if 0 < n <= maximum and all(sorted(row) == list(range(n)) for row in table):
                unique.setdefault(tuple(map(tuple, table)), table)
    return sorted(unique.values(), key=len)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--equation", type=int, action="append", required=True)
    parser.add_argument("--seconds", type=float, default=5)
    parser.add_argument("--max-order", type=int, default=12)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.seconds <= 0 or args.max_order < 1 or any(not 1 <= n <= 4694 for n in args.equation):
        parser.error("Use positive search limits and equation numbers from 1 through 4694.")
    equations, results = load_equations(), []
    for number in args.equation:
        tables = saved_sources(number, args.max_order)
        if not tables:
            parser.error(f"No saved left-quasigroup sources for E{number} within the order bound.")
        for index, table in enumerate(tables):
            assert satisfies(*equations[number - 1], sum(table, []), len(table))
            result = solve(table, equations[number - 1], args.seconds)
            result.update(equation=number, index=index)
            results.append(result)
            args.output.write_text(json.dumps(results, indent=2) + "\n")
            print(number, index, len(table), result["status"], round(result["seconds"], 3), flush=True)
            if result["status"] == "sat":
                break


if __name__ == "__main__":
    main()

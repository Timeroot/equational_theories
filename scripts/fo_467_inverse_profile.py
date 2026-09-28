#!/usr/bin/env python3
"""Bounded homogeneous E467 search using inverse-permutation normalization.

Research only: UNSAT excludes scalar-equivariant targets, not general models.
Every SAT witness is independently checked on the whole multiplication table.
"""
import argparse
import json
from pathlib import Path
import time

from fo_704_467_research import verify


def solve(p, s, seconds, workers=1, product=True):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    f = [m.NewIntVar(0, p-1, f"f{i}") for i in range(p)]
    g = [m.NewIntVar(0, p-1, f"g{i}") for i in range(p)]
    c = m.NewIntVar(1, p-1, "zero_row")
    m.AddInverse(f, g)
    m.Add(f[0] != 0)
    m.Add(f[1] == s)
    m.Add(f[s] == pow(s, -1, p))
    m.Add(f[s*s % p] == s*s % p)
    m.AddAllowedAssignments([c, g[0]],
                            [(v, v*v*s % p) for v in range(1, p)])
    if product:
        # Multiplying the nonzero values of the row and right profile gives
        # f(0) = -c*g(0) = -c^3*s. This is valid for every homogeneous Latin
        # operation over an odd prime field, not an affine assumption.
        m.AddAllowedAssignments([c, f[0]],
                                [(v, -v**3*s % p) for v in range(1, p)])
    ff0 = m.NewIntVar(1, p-1, "ff0")
    m.AddElement(f[0], f, ff0)
    m.AddAllowedAssignments([c, ff0],
                            [(v, pow(v, -1, p)) for v in range(1, p)])
    quotients = []
    sinv = pow(s, -1, p)
    for t in range(1, p):
        ff = m.NewIntVar(0, p-1, f"ff{t}")
        m.AddElement(f[t], f, ff)
        # f(f(t)) = (t/s) * g(s/t).
        k, j = t*sinv % p, s*pow(t, -1, p) % p
        m.AddAllowedAssignments([ff, g[j]], [(k*v % p, v) for v in range(p)])
        qt = m.NewIntVar(0, p-1, f"q{t}")
        m.AddAllowedAssignments([f[t], qt],
                                [(v, v*pow(t, -1, p) % p) for v in range(p)])
        quotients.append(qt)
    m.AddAllDifferent([c] + quotients)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    started = time.monotonic()
    status = solver.Solve(m)
    result = {"prime": p, "square_multiplier": s, "product_constraint": product,
              "status": solver.StatusName(status), "seconds": time.monotonic()-started,
              "branches": solver.NumBranches(), "conflicts": solver.NumConflicts()}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        ff = [solver.Value(v) for v in f]
        cc = solver.Value(c)
        assert verify(p, cc, ff)
        result.update(c=cc, f=ff, independently_verified=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=47)
    parser.add_argument("--square", type=int, action="append", required=True)
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--no-product", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = {"status": "research only; no Lean search certificate", "searches": []}
    for s in args.square:
        row = solve(args.prime, s, args.seconds, args.workers, not args.no_product)
        out["searches"].append(row)
        print(json.dumps(row), flush=True)
        if args.output:
            args.output.write_text(json.dumps(out, indent=2) + "\n")

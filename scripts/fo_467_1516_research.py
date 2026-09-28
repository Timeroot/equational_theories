#!/usr/bin/env python3
"""Symmetry-reduced E1516 research, not a Lean proof or a full spectrum search.

For prime p, a multiplication equivariant under all nonzero scalings has
M(0,y)=c*y and M(x,y)=x*f(y/x) for x != 0.  Its E1516 identity reduces to
the constraints below. Every positive answer is checked on all p*p pairs.
Infeasibility excludes only the specified symmetry and square multiplier.
"""

import argparse
import json
from pathlib import Path
import time


def scalar_checks(p):
    """Exact elementary finite calculations, independently of the solver."""
    return {
        "prime": p,
        "E467_scalar_coefficients": [
            [a, b] for a in range(p) for b in range(p)
            if (a*b*(b+1)-1) % p == 0 and (a*b**3+a+b**4) % p == 0
        ],
        "E1516_scalar_coefficients": [
            [a, b] for a in range(p) for b in range(p)
            if (a*b*(b+1)-1) % p == 0 and (a*a+a*b+b**3) % p == 0
        ],
        "E63_GL_roots": [b for b in range(p) if (b**5+b**4+1) % p == 0],
        "E1516_GL_allowed_square_multipliers": sorted({
            -pow(b, 4, p)*(1+b) % p for b in range(1, p-1)
        }),
    }


def verify(p, c, f):
    def op(x, y):
        return c*y % p if x == 0 else x*f[y*pow(x, -1, p) % p] % p
    assert all(op(op(y, y), op(x, op(x, y))) == x
               for x in range(p) for y in range(p))
    assert all(op(t*x % p, t*y % p) == t*op(x, y) % p
               for t in range(1, p) for x in range(p) for y in range(p))
    return True


def solve(p, s, seconds):
    from ortools.sat.python import cp_model

    m = cp_model.CpModel()
    f = [m.NewIntVar(0, p-1, f"f{i}") for i in range(p)]
    c = m.NewIntVar(1, p-1, "c")
    m.Add(f[0] != 0)
    m.Add(f[1] == s)
    m.AddAllDifferent(f)
    inv = lambda t: pow(t, -1, p)

    # The original equation at (x,y)=(1,0) and (0,1).
    d = m.NewIntVar(1, p-1, "d")
    m.AddElement(f[0], f, d)
    m.AddAllowedAssignments([c, d], [[v, inv(v)] for v in range(1, p)])
    z = m.NewIntVar(1, p-1, "z")
    m.AddAllowedAssignments([c, z], [[v, v*v*inv(s) % p] for v in range(1, p)])
    m.AddElement(z, f, 0)

    quotients = []
    for t in range(1, p):
        # E1516 at (1,t): f(f(f(t))/(s*t)) = 1/(s*t).
        k = inv(s*t % p)
        ff = m.NewIntVar(0, p-1, f"ff{t}")
        idx = m.NewIntVar(0, p-1, f"idx{t}")
        m.AddElement(f[t], f, ff)
        m.AddAllowedAssignments([ff, idx], [[v, k*v % p] for v in range(p)])
        m.AddElement(idx, f, k)

        # Right cancellation, a theorem for every finite E1516 magma.
        q = m.NewIntVar(0, p-1, f"q{t}")
        m.AddAllowedAssignments([f[t], q], [[v, inv(t)*v % p] for v in range(p)])
        quotients.append(q)
    m.AddAllDifferent([c] + quotients)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 1
    started = time.monotonic()
    result = solver.Solve(m)
    record = {"p": p, "s": s, "status": solver.StatusName(result),
              "seconds": time.monotonic()-started}
    if result in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        record.update(c=solver.Value(c), f=[solver.Value(v) for v in f])
        record["directly_verified"] = verify(p, record["c"], record["f"])
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=41)
    parser.add_argument("--seconds", type=float, default=4)
    parser.add_argument("--square", type=int, action="append")
    parser.add_argument("--scalar-only", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    p = args.prime
    assert p > 2 and all(p % d for d in range(2, int(p**0.5)+1)), "odd prime required"
    result = {"status": "research evidence; no Lean solver certificate",
              "scalar_checks": scalar_checks(p), "searches": []}
    if not args.scalar_only:
        for s in args.square or range(1, p):
            assert 0 < s < p
            row = solve(p, s, args.seconds)
            result["searches"].append(row)
            print(json.dumps(row), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

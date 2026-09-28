#!/usr/bin/env python3
"""Symmetry-reduced E1516 search with inverse-permutation propagation.

An infeasible result concerns the specified homogeneous operation class only.
The historical CP-SAT runs have been superseded by a complete Lean proof
using separate LRAT certificates; see fo_1516_certificates.py. Positive
results and source coefficients are independently checked on full tables.

Default: check saved evidence. --search PRIME SECONDS [--square S ...] reruns
bounded CP-SAT searches. A timeout never means an exclusion.
"""

import argparse
import json
from pathlib import Path
import time

from fo_467_1516_research import verify
from spectrum_generate import evaluate, load_equations

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/spectrum/fo_1516_homogeneous29.json"


def solve(p, s, seconds, workers=4):
    from ortools.sat.python import cp_model

    m = cp_model.CpModel()
    f = [m.NewIntVar(0, p-1, f"f{i}") for i in range(p)]
    inverse_f = [m.NewIntVar(0, p-1, f"g{i}") for i in range(p)]
    c = m.NewIntVar(1, p-1, "c")
    m.AddInverse(f, inverse_f)
    m.Add(f[0] != 0)
    m.Add(f[1] == s)
    inv = lambda t: pow(t, -1, p)

    def lookup(x, name):
        value = m.NewIntVar(0, p-1, name)
        m.AddElement(x, f, value)
        return value

    # E1516 at (x,y)=(0,1) and (1,0), respectively.
    m.AddAllowedAssignments([c, inverse_f[0]],
                            [(u, u*u*inv(s) % p) for u in range(1, p)])
    ff0 = lookup(f[0], "ff0")
    m.AddAllowedAssignments([c, ff0], [(u, inv(u)) for u in range(1, p)])

    quotients = []
    for t in range(1, p):
        # f(f(f(t))/(s*t))=1/(s*t), equivalently
        # f(f(t))=s*t*inverse_f[1/(s*t)].
        ff = lookup(f[t], f"ff{t}")
        k = inv(s*t % p)
        m.AddAllowedAssignments([ff, inverse_f[k]],
                                [(u, k*u % p) for u in range(p)])
        quotient = m.NewIntVar(0, p-1, f"q{t}")
        m.AddAllowedAssignments([f[t], quotient],
                                [(u, inv(t)*u % p) for u in range(p)])
        quotients.append(quotient)
    # Right cancellation is valid for every finite E1516 model.
    m.AddAllDifferent([c] + quotients)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 1
    started = time.monotonic()
    status = solver.Solve(m)
    result = dict(p=p, s=s, status=solver.StatusName(status),
                  seconds=time.monotonic()-started,
                  branches=solver.NumBranches(), conflicts=solver.NumConflicts())
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        result.update(c=solver.Value(c), f=[solver.Value(v) for v in f])
        result["verified"] = verify(p, result["c"], result["f"])
    return result


def check_saved():
    record = json.loads(DATA.read_text())
    assert record["prime"] == 29 and record["law"] == 1516
    rows = {row["s"]: row for row in record["searches"]}
    assert set(rows) == set(range(1, 29))
    assert rows[1]["status"] in ("OPTIMAL", "FEASIBLE")
    verify(29, rows[1]["c"], rows[1]["f"])
    assert all(rows[s]["status"] == "INFEASIBLE" for s in range(2, 29))
    allowed = sorted({-pow(b, 4, 29)*(b+1) % 29 for b in range(1, 28)})
    assert record["allowed_GL_square_multipliers"] == allowed
    assert 1 not in allowed
    equations = load_equations()
    for law, (a, b) in record["source_coefficients"].items():
        table = [(a*x+b*y) % 29 for x in range(29) for y in range(29)]
        lhs, rhs = equations[int(law)-1]
        for x in range(29):
            for y in range(29):
                v = {"x": x, "y": y}
                assert evaluate(lhs, v, table, 29) == evaluate(rhs, v, table, 29)
    for order in (31, 41):
        seed = json.loads((ROOT / f"data/spectrum/63_idempotent{order}.json").read_text())
        assert seed["p"] == order and seed["s"] == 1 and seed["f"][1] == 1
        verify(order, seed["c"], seed["f"])
    print("Checked four source tables, the homogeneous positive model, and GL parameter coverage.")
    print("Checked the new idempotent E63/E1516 seeds of orders 31 and 41.")
    print("Historical CP-SAT results checked; the completed Lean classification uses the separate LRAT certificates.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", nargs=2, metavar=("PRIME", "SECONDS"))
    parser.add_argument("--square", type=int, action="append")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not args.search:
        check_saved()
        return
    p, seconds = int(args.search[0]), float(args.search[1])
    assert p > 2 and all(p % d for d in range(2, int(p**0.5)+1))
    results = []
    for s in args.square or range(1, p):
        assert 0 < s < p
        result = solve(p, s, seconds, args.workers)
        print(json.dumps(result), flush=True)
        results.append(result)
    if args.output:
        args.output.write_text(json.dumps(results, indent=2)+"\n")


if __name__ == "__main__":
    main()

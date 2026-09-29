#!/usr/bin/env python3
"""Bounded E907 searches using the inverse of every left translation.

E907 makes every left translation surjective, hence bijective in a finite
model. Its equation is equivalently p(p(y,x),p(x,y)) = inverse_L_y(x).
This is a full finite-model encoding; no right cancellation is assumed.
Timeouts prove nothing, and infeasible statuses are not Lean certificates.
"""
import argparse
import json
from pathlib import Path
import time

from spectrum_generate import load_equations, satisfies


def solve(n, seconds, idempotent=False, workers=4):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    table = [m.NewIntVar(0, n-1, f'p{x}_{y}') for x in range(n) for y in range(n)]
    inverse = [[m.NewIntVar(0, n-1, f'g{x}_{y}') for y in range(n)] for x in range(n)]
    diag = [table[x*n+x] for x in range(n)]
    for y in range(n):
        m.AddInverse(table[y*n:(y+1)*n], inverse[y])
        if idempotent:
            m.Add(diag[y] == y)
        for x in range(n):
            index = m.NewIntVar(0, n*n-1, f'i{x}_{y}')
            m.Add(index == n*table[y*n+x]+table[x*n+y])
            m.AddElement(index, table, inverse[y][x])
        m.AddElement(diag[y], diag, inverse[y][y])
    m.AddAllowedAssignments([table[0]], [(0,), (1,)])
    if n == 7 and not idempotent:
        for x in range(n):
            for y in range(n):
                m.AddHint(table[x*n+y], (4*x+y) % n)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 1
    start = time.monotonic()
    status = solver.Solve(m)
    row = dict(law=907, order=n, idempotent=idempotent,
               status=solver.StatusName(status), seconds=time.monotonic()-start,
               limit_seconds=seconds, workers=workers,
               branches=solver.NumBranches(), conflicts=solver.NumConflicts(),
               lean_proof=False)
    if status in [cp_model.OPTIMAL, cp_model.FEASIBLE]:
        values = [solver.Value(v) for v in table]
        assert satisfies(*load_equations()[906], values, n)
        assert not idempotent or all(values[x*n+x] == x for x in range(n))
        row.update(table=values, full_original_law_verified=True)
    return row


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('order', type=int)
    p.add_argument('--seconds', type=float, default=120)
    p.add_argument('--idempotent', action='store_true')
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    assert args.order >= 2 and args.seconds > 0
    result = solve(args.order, args.seconds, args.idempotent, args.workers)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)

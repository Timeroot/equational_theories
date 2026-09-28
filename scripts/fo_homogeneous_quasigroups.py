#!/usr/bin/env python3
"""Bounded homogeneous E704/E1110 searches with inverse-row propagation.

Positive models are independently checked against all instances of the original
law. Infeasibility applies only to the specified homogeneous operation class;
solver statuses are research evidence, not Lean proofs or spectrum exclusions.
"""
import argparse
import json
from pathlib import Path
import time

from spectrum_generate import evaluate, load_equations


def verify(p, law, c, f):
    table = [c*y % p if x == 0 else x*f[y*pow(x, -1, p) % p] % p
             for x in range(p) for y in range(p)]
    lhs, rhs = load_equations()[law-1]
    for x in range(p):
        for y in range(p):
            v = {'x': x, 'y': y}
            assert evaluate(lhs, v, table, p) == evaluate(rhs, v, table, p), (x, y)
    return True


def solve(p, law, s, seconds, workers=4):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    f = [m.NewIntVar(0, p-1, f'f{i}') for i in range(p)]
    g = [m.NewIntVar(0, p-1, f'g{i}') for i in range(p)]
    c = m.NewIntVar(1, p-1, 'c')
    m.AddInverse(f, g)
    m.Add(f[0] != 0)
    m.Add(f[1] == s)
    inv = lambda x: pow(x % p, -1, p)
    # Both laws give c²*s*f(0)=1. Multiplying the nonzero entries of
    # the row and right-column permutations gives f(0)=-c*g(0).
    m.AddAllowedAssignments([c, f[0], g[0]], [
        (a, inv(a*a*s), -inv(a*a*a*s) % p) for a in range(1, p)
    ])
    profile = [c] + [m.NewIntVar(0, p-1, f'r{i}') for i in range(1, p)]
    for t in range(1, p):
        if law == 704:
            m.AddAllowedAssignments([f[t], profile[t]], [(a, a*inv(t) % p) for a in range(p)])
        else:
            m.AddAllowedAssignments([f[inv(t)], profile[t]], [(a, a*t % p) for a in range(p)])
    m.AddAllDifferent(profile)
    # Consequences at the unique zero of f, propagated explicitly.
    if law == 704:
        at_zero = m.NewIntVar(0, p-1, 'f_f0')
        m.AddElement(f[0], f, at_zero)
        m.AddAllowedAssignments([c, at_zero], [(a, -a**3 % p) for a in range(1, p)])
    else:
        index = m.NewIntVar(1, p-1, 'c2s')
        value = m.NewIntVar(1, p-1, 'minus_inverse_c')
        m.AddAllowedAssignments([c, index, value], [
            (a, a*a*s % p, -inv(a) % p) for a in range(1, p)
        ])
        m.AddElement(index, f, value)
    for t in range(p):
        if law == 704:
            # f²(r(t)) = (s*t)⁻¹, with inverse(0)=0.
            m.AddElement(profile[t], f, g[inv(s*t) if t else 0])
        elif law == 1110:
            # f(R(f(t))) = t/s, equivalently R(f(t))=g(t/s).
            m.AddElement(f[t], profile, g[t*inv(s) % p])
        else:
            raise ValueError(law)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 1
    started = time.monotonic()
    status = solver.Solve(m)
    result = dict(prime=p, law=law, multiplier=s, status=solver.StatusName(status),
                  seconds=time.monotonic()-started, branches=solver.NumBranches(),
                  conflicts=solver.NumConflicts())
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        result.update(c=solver.Value(c), f=[solver.Value(v) for v in f])
        result['verified'] = verify(p, law, result['c'], result['f'])
    return result


def representatives(p):
    by_order = {}
    for s in range(1, p):
        order = next(k for k in range(1, p) if pow(s, k, p) == 1)
        by_order.setdefault(order, s)
    return [s for _, s in sorted(by_order.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('law', type=int, choices=(704, 1110))
    parser.add_argument('prime', type=int)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--multiplier', type=int, action='append')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    p = args.prime
    assert p > 2 and all(p % d for d in range(2, int(p**0.5)+1))
    rows = []
    for s in args.multiplier or representatives(p):
        assert 0 < s < p
        r = solve(p, args.law, s, args.seconds, args.workers)
        rows.append(r)
        print(json.dumps(r), flush=True)
        if args.output:
            args.output.write_text(json.dumps(rows, indent=2)+'\n')


if __name__ == '__main__':
    main()

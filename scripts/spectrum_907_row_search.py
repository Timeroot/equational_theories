#!/usr/bin/env python3
"""Bounded E907 searches split by canonical first-row cycle forms.

E907 makes every left translation surjective, hence bijective in a finite
model. Relabeling while fixing zero reduces row zero to these pointed cycle
forms. All forms, including the identity, must be refuted for an exclusion.
The extra inverse clauses are justified by Spectrum.E907.left_division.
No right cancellation or idempotence is assumed. SAT answers are checked
against the original equation; UNSAT answers here are external evidence.
Order eight is independently replayed in Spectrum.Equation907Eight.

Requires python-sat. A conflict budget or time limit leaves UNKNOWN cases;
neither is interpreted as nonexistence.
"""
import argparse
import datetime
import hashlib
import itertools
import json
from pathlib import Path
import time

import pysat
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from spectrum_generate import load_equations, satisfies


def partitions(n, cap=None):
    if n == 0:
        yield []
    else:
        for k in range(min(n, n if cap is None else cap), 0, -1):
            for tail in partitions(n-k, k):
                yield [k, *tail]


def canonical_rows(n):
    for k in range(1, n+1):
        for tail in partitions(n-k):
            row, start = list(range(n)), 0
            for length in [k, *tail]:
                for j in range(length):
                    row[start+j] = start+(j+1) % length
                start += length
            yield k, tail, row


def solve(n, budgets=(10000, 100000), seconds=300, short_cycles=False):
    start = time.monotonic()
    forms = list(canonical_rows(n))
    results, attempts = {}, []
    def atom(x, y, z):
        return 1+(x*n+y)*n+z
    with Solver(name='cadical195') as solver:
        top = n**3
        # One output per table cell, and every output occurs once per row.
        for x, y in itertools.product(range(n), repeat=2):
            for values in ([atom(x,y,z) for z in range(n)],
                           [atom(x,z,y) for z in range(n)]):
                cnf = CardEnc.equals(values, 1, top_id=top, encoding=EncType.seqcounter)
                top = cnf.nv
                solver.append_formula(cnf.clauses)
        for x,y,a,b,c in itertools.product(range(n), repeat=5):
            # Given y*x=a and x*y=b, a*b=c iff y*c=x.
            u,v = atom(y,x,a),atom(x,y,b)
            solver.add_clause([-u,-v,-atom(a,b,c),atom(y,c,x)])
            solver.add_clause([-u,-v,-atom(y,c,x),atom(a,b,c)])
        if short_cycles:
            # E907.PointedCycles proves that a nontrivial cycle of L_a
            # containing a has length at least five, in every finite model.
            for a in range(n):
                other = [b for b in range(n) if b != a]
                for k in (2, 3, 4):
                    for tail in itertools.permutations(other, k - 1):
                        cycle = (a, *tail, a)
                        solver.add_clause([
                            -atom(a, cycle[j], cycle[j + 1]) for j in range(k)
                        ])
        stopped = False
        for budget in budgets:
            for i,(k,tail,row) in enumerate(forms):
                if i in results and results[i]['status'] != 'UNKNOWN':
                    continue
                if time.monotonic()-start >= seconds:
                    stopped = True
                    break
                solver.conf_budget(budget)
                before = time.monotonic()
                answer = solver.solve_limited(assumptions=[atom(0,j,row[j]) for j in range(n)])
                entry = dict(case=i, zero_cycle=k, other_cycles=tail, row=row,
                             budget=budget, seconds=time.monotonic()-before,
                             status='SAT' if answer else 'UNSAT' if answer is False else 'UNKNOWN')
                if answer:
                    model = set(solver.get_model())
                    table = [next(z for z in range(n) if atom(x,y,z) in model)
                             for x,y in itertools.product(range(n), repeat=2)]
                    assert satisfies(*load_equations()[906], table, n)
                    entry.update(table=table, original_law_verified=True)
                results[i] = entry
                attempts.append(entry)
                print(json.dumps(dict(order=n, **entry)), flush=True)
                if answer:
                    stopped = True
                    break
            if stopped:
                break
    return dict(order=n, case_count=len(forms), results=list(results.values()), attempts=attempts,
                external_refutation_complete=len(results)==len(forms) and
                    all(r['status']=='UNSAT' for r in results.values()),
                seconds=time.monotonic()-start, time_limit_seconds=seconds,
                conflict_budgets=list(budgets), short_cycle_constraints=short_cycles,
                lean_proof=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('orders', nargs='+', type=int)
    parser.add_argument('--budgets', nargs='+', type=int, default=[10000,100000])
    parser.add_argument('--seconds', type=float, default=300,
                        help='Per-order budget, checked between conflict-limited calls')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--short-cycles', action='store_true',
                        help='Use the proved pointed-cycle exclusions in every row')
    args = parser.parse_args()
    if min(args.orders)<2 or min(args.budgets)<=0 or args.seconds<=0:
        parser.error('Orders must be at least two; budgets must be positive')
    report = dict(law=907, date=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  script='scripts/spectrum_907_row_search.py',
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  solver='cadical195', python_sat_version=pysat.__version__, searches=[])
    for n in args.orders:
        report['searches'].append(solve(n, args.budgets, args.seconds, args.short_cycles))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print('Wrote',args.output,flush=True)


if __name__ == '__main__':
    main()

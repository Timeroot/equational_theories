#!/usr/bin/env python3
"""Bounded finite E63 search via left division and canonical translation cycles.

Requires python-sat. Results are discovery evidence, not Lean certificates.
See docs/63_spectrum_progress.md for completeness of the cycle-type split.
"""
import argparse
import json
from itertools import product
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

from spectrum_generate import load_equations, satisfies


def partitions(total, minimum):
    if total == 0:
        yield []
    for size in range(minimum, total + 1):
        if size != 2:
            for rest in partitions(total - size, size):
                yield [size, *rest]


def search(n, idempotent, budget):
    solver = Solver(name='cadical195')

    def cell(x, y, z):
        return 1 + x * n * n + y * n + z

    top = n**3
    for x, y in product(range(n), repeat=2):
        for variables in ([cell(x, y, z) for z in range(n)],
                          [cell(x, z, y) for z in range(n)],
                          [cell(z, x, y) for z in range(n)]):
            encoding = CardEnc.equals(variables, 1, top_id=top, encoding=EncType.seqcounter)
            top = encoding.nv
            solver.append_formula(encoding.clauses)
    if idempotent:
        for x in range(n):
            solver.add_clause([cell(x, x, x)])
    # E229: (y*(y*x))*y=x. In the finite setting this is equivalent to E125,
    # and its left-division operation satisfies E63.
    for x, y, a, b in product(range(n), repeat=4):
        solver.add_clause([-cell(y, x, a), -cell(y, a, b), cell(b, y, x)])

    results = []
    for distinguished in ([1] if idempotent else [1, 3]):
        for other_cycles in partitions(n - distinguished, 3 if idempotent else 1):
            cycles = [distinguished, *other_cycles]
            row, offset = [], 0
            for length in cycles:
                row.extend(offset + (i + 1) % length for i in range(length))
                offset += length
            assumptions = [cell(0, x, row[x]) for x in range(n)]
            solver.conf_budget(budget)
            result = solver.solve_limited(assumptions=assumptions)
            status = 'SAT' if result is True else 'UNSAT' if result is False else 'UNKNOWN'
            print(cycles, status, flush=True)
            record = {'cycles': cycles, 'status': status}
            results.append(record)
            if result is True:
                model = set(solver.get_model())
                table = [[next(z for z in range(n) if cell(x, y, z) in model)
                          for y in range(n)] for x in range(n)]
                equations = load_equations()
                assert satisfies(*equations[228], [z for row in table for z in row], n)
                # Compute left division and independently evaluate the original law.
                e63 = [table[x].index(y) for x, y in product(range(n), repeat=2)]
                assert satisfies(*equations[62], e63, n)
                if idempotent:
                    assert all(e63[x * n + x] == x for x in range(n))
                record['e63_table'] = e63
                solver.delete()
                return results
    solver.delete()
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=10)
    parser.add_argument('--idempotent', action='store_true')
    parser.add_argument('--conflicts', type=int, default=1_000_000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.order < 3 or args.conflicts < 1:
        parser.error('Use order >= 3 and a positive conflict budget.')
    cases = search(args.order, args.idempotent, args.conflicts)
    report = {'law': 63, 'order': args.order, 'idempotent_only': args.idempotent,
              'evidence': 'SAT_SOLVER_NOT_LEAN', 'cases': cases}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    if any(case['status'] == 'SAT' for case in cases):
        print('Found an independently evaluated E63 table.')
    elif all(case['status'] == 'UNSAT' for case in cases):
        print(f'All {len(cases)} canonical cases were refuted. No Lean proof is asserted.')
    else:
        print('Unresolved cases remain; no exclusion follows.')


if __name__ == '__main__':
    main()

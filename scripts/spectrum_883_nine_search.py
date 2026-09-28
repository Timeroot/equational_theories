#!/usr/bin/env python3
"""Reproduce the external E883 order-nine refutation by first-row cycle forms.

Requires python-sat. This is an external search, not a Lean proof oracle.
Every nontrivial Latin square has a nonidentity row. After choosing its index
as zero, conjugation fixing zero puts that row into one of the 66 nonidentity
forms below. The identity form is also searched, but need not be refuted.
"""
import argparse
import itertools
import json
import time
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

N = 9


def var(x, y, z):
    return 1 + x * N * N + y * N + z


def partitions(n, cap=None):
    if n == 0:
        yield []
        return
    for a in range(min(n, n if cap is None else cap), 0, -1):
        for tail in partitions(n - a, a):
            yield [a] + tail


def canonical_rows():
    for k in range(1, N + 1):
        for tail in partitions(N - k):
            row, start = list(range(N)), 0
            for length in [k] + tail:
                for j in range(length):
                    row[start + j] = start + (j + 1) % length
                start += length
            yield (k, tuple(tail)), row


def solver():
    s = Solver(name='cadical195')
    top = N ** 3
    for x, y in itertools.product(range(N), repeat=2):
        for vs in ([var(x, y, z) for z in range(N)],
                   [var(x, z, y) for z in range(N)],
                   [var(z, x, y) for z in range(N)]):
            cnf = CardEnc.equals(vs, 1, top_id=top, encoding=EncType.seqcounter)
            top = cnf.nv
            s.append_formula(cnf.clauses)
    s.add_clause([var(0, 0, 0), var(0, 0, 1)])
    for x, y, d, u, w in itertools.product(range(N), repeat=5):
        s.add_clause([-var(y, y, d), -var(x, y, u), -var(u, d, w), var(y, w, x)])
    return s


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--first-conflicts', type=int, default=10000)
    p.add_argument('--second-conflicts', type=int, default=200000)
    p.add_argument('--output', type=Path, default=Path('/tmp/e883-nine-refutation.json'))
    args = p.parse_args()
    start = time.monotonic()
    forms = list(canonical_rows())
    assert len(forms) == 67 and len({tuple(row) for _, row in forms}) == 67
    results = {}
    for budget in (args.first_conflicts, args.second_conflicts):
        with solver() as s:
            for key, row in forms:
                if key in results and results[key]['status'] != 'UNKNOWN':
                    continue
                s.conf_budget(budget)
                result = s.solve_limited(assumptions=[var(0, j, row[j]) for j in range(N)])
                status = 'SAT' if result else 'UNSAT' if result is False else 'UNKNOWN'
                item = {'zero_cycle': key[0], 'other_cycles': list(key[1]), 'status': status}
                if result:
                    model = set(s.get_model())
                    table = [next(z for z in range(N) if var(x, y, z) in model)
                             for x, y in itertools.product(range(N), repeat=2)]
                    from spectrum_generate import load_equations, satisfies
                    assert satisfies(*load_equations()[882], table, N)
                    item['table'] = table
                results[key] = item
                print(json.dumps(item), flush=True)
                if result:
                    break
        if any(item['status'] == 'SAT' for item in results.values()):
            break
    identity = (1, (1,) * 8)
    refuted = len(results) == 67 and all(
        item['status'] == 'UNSAT' for key, item in results.items() if key != identity)
    output = {'law': 883, 'order': N, 'external_refutation_complete': refuted,
              'seconds': time.monotonic() - start, 'cases': list(results.values())}
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(f'All 66 nonidentity forms refuted: {refuted}', flush=True)
    return 0 if refuted else 1


if __name__ == '__main__':
    raise SystemExit(main())

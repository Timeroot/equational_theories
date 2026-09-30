#!/usr/bin/env python3
"""Bounded probes of possible E907 structure theorems.

These are searches for counterexamples to explicitly named hypotheses. They
assume only E907 and its proved finite left cancellation, except for the
idempotent/midpoint modes, whose added restrictions are stated below.
UNSAT at one order is not a general theorem; UNKNOWN establishes nothing.
Requires python-sat. Every returned table is checked against the original law
and the requested extra constraints.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from spectrum_generate import load_equations, satisfies

PROPERTIES = ('right_incident', 'right_nonincident', 'square', 'idempotent_term',
              'no_idempotent', 'idempotent', 'midpoint_left', 'midpoint_latin')


def probe(n, mode, budget=200000):
    start = time.monotonic()
    def atom(x, y, z):
        return 1 + (x*n+y)*n+z
    top = n**3
    with Solver(name='cadical195') as solver:
        def exactly_one(values):
            nonlocal top
            cnf = CardEnc.equals(values, 1, top_id=top, encoding=EncType.seqcounter)
            top = cnf.nv
            solver.append_formula(cnf.clauses)

        for x, y in itertools.product(range(n), repeat=2):
            exactly_one([atom(x, y, z) for z in range(n)])
            exactly_one([atom(x, z, y) for z in range(n)])
        for x, y, a, b, c in itertools.product(range(n), repeat=5):
            u, v = atom(y, x, a), atom(x, y, b)
            solver.add_clause([-u, -v, -atom(a, b, c), atom(y, c, x)])
            solver.add_clause([-u, -v, -atom(y, c, x), atom(a, b, c)])

        if mode.startswith('right_'):
            a, b = (0, 1) if mode == 'right_incident' else (1, 2)
            for z in range(n):
                solver.add_clause([-atom(a, 0, z), atom(b, 0, z)])
        elif mode == 'square':
            for z in range(n):
                solver.add_clause([-atom(0, 0, z), atom(1, 1, z)])
        elif mode == 'idempotent_term':
            for a, e in itertools.product(range(n), repeat=2):
                solver.add_clause([-atom(0, 0, a), -atom(a, 0, e), -atom(e, e, e)])
            # A violating element is not idempotent, so relabel its square as 1.
            solver.add_clause([atom(0, 0, 1)])
        elif mode == 'no_idempotent':
            for x in range(n):
                solver.add_clause([-atom(x, x, x)])
        elif mode == 'idempotent' or mode.startswith('midpoint_'):
            for x in range(n):
                solver.add_clause([atom(x, x, x)])
            if mode == 'midpoint_latin':
                for y, z in itertools.product(range(n), repeat=2):
                    exactly_one([atom(x, y, z) for x in range(n)])
            if mode.startswith('midpoint_'):
                def left_wire(row, arg):
                    nonlocal top
                    out = list(range(top+1, top+n+1))
                    top += n
                    exactly_one(out)
                    for j, k in itertools.product(range(n), repeat=2):
                        solver.add_clause([-arg[j], -atom(row, j, k), out[k]])
                    return out
                a = left_wire(1, left_wire(1, [atom(0, 1, k) for k in range(n)]))
                b = left_wire(0, left_wire(0, [atom(1, 0, k) for k in range(n)]))
                for k in range(n):
                    solver.add_clause([-a[k], -b[k]])
        else:
            raise ValueError(mode)

        solver.conf_budget(budget)
        answer = solver.solve_limited()
        result = dict(order=n, mode=mode, budget=budget,
                      status='SAT' if answer else 'UNSAT' if answer is False else 'UNKNOWN',
                      seconds=time.monotonic()-start, lean_proof=False)
        if answer:
            model = set(solver.get_model())
            table = [next(z for z in range(n) if atom(x, y, z) in model)
                     for x, y in itertools.product(range(n), repeat=2)]
            assert satisfies(*load_equations()[906], table, n)
            op = lambda x, y: table[x*n+y]
            if mode.startswith('right_'):
                a, b = (0, 1) if mode == 'right_incident' else (1, 2)
                assert op(a, 0) == op(b, 0)
            elif mode == 'square':
                assert op(0, 0) == op(1, 1)
            elif mode == 'idempotent_term':
                e = op(op(0, 0), 0)
                assert op(e, e) != e
            elif mode == 'no_idempotent':
                assert all(op(x, x) != x for x in range(n))
            else:
                assert all(op(x, x) == x for x in range(n))
                if mode.startswith('midpoint_'):
                    assert op(1, op(1, op(0, 1))) != op(0, op(0, op(1, 0)))
                if mode == 'midpoint_latin':
                    assert all(len({op(x, y) for x in range(n)}) == n for y in range(n))
            result.update(table=table, original_law_verified=True, extra_constraints_verified=True)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('orders', nargs='+', type=int)
    parser.add_argument('--properties', nargs='+', choices=PROPERTIES, default=list(PROPERTIES))
    parser.add_argument('--budget', type=int, default=200000)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if min(args.orders) < 3 or args.budget <= 0:
        parser.error('Orders must be at least three and the conflict budget positive')
    results = []
    for n in args.orders:
        for mode in args.properties:
            result = probe(n, mode, args.budget)
            results.append(result)
            print(json.dumps(result), flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(dict(law=907, solver='cadical195', searches=results), indent=2)+'\n')


if __name__ == '__main__':
    main()

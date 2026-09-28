#!/usr/bin/env python3
"""Check the scalar data in the E1279 finite-FO transfer investigation.

The default action checks finite source tables and root obstructions; it does
not call a solver. --search makes a bounded Z3 search for a target operation
commuting with multiplication by a primitive root on F_p. A timeout is unknown,
and an UNSAT result would still need an independently checked proof.
"""
import argparse
import json
import time
from pathlib import Path

from spectrum_generate import evaluate, load_equations

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data/definability_fo_1279_transfers.json'


def checked_data():
    equations = load_equations()
    sources = []
    for law, p, a, b in [(1279, 29, 4, 11), (1110, 29, 6, 28),
                          (1279, 47, 42, 38), (1279, 71, 14, 36),
                          (1279, 73, 3, 28)]:
        table = [(a*x+b*y) % p for x in range(p) for y in range(p)]
        lhs, rhs = equations[law-1]
        for x in range(p):
            for y in range(p):
                valuation = {'x': x, 'y': y}
                assert evaluate(lhs, valuation, table, p) == evaluate(rhs, valuation, table, p)
        sources.append(dict(law=law, prime=p, a=a, b=b, checked_assignments=p*p))
    roots = {str(p): [d for d in range(p) if (d**5+d**4+1) % p == 0]
             for p in [29, 41, 47, 71, 73]}
    assert all(roots[str(p)] == [] for p in [29, 41, 47, 71])
    return dict(source_checks=sources, E63_polynomial='d^5+d^4+1', roots=roots)


def primitive_root(p):
    for g in range(1, p):
        if len({pow(g, k, p) for k in range(p-1)}) == p-1:
            return g
    raise ValueError('No primitive root; use a prime order.')


def search(p, law, seconds, latin=False):
    import z3
    started = time.monotonic()
    sort = z3.FiniteDomainSort('F', p)
    vals = [z3.FiniteDomainVal(i, sort) for i in range(p)]
    op = z3.Function('op', sort, sort, sort)
    scale = z3.Function('scale', sort, sort)
    solver = z3.Solver()
    solver.set(timeout=seconds*1000)
    g = primitive_root(p)
    for i in range(p):
        solver.add(scale(vals[i]) == vals[i*g % p])
    for x in range(p):
        for y in range(p):
            solver.add(op(vals[x*g % p], vals[y*g % p]) == scale(op(vals[x], vals[y])))
    def ev(term, x, y):
        if isinstance(term, str):
            return x if term == 'x' else y
        return op(ev(term[0], x, y), ev(term[1], x, y))
    lhs, rhs = load_equations()[law-1]
    for x, y in [(0, 0), (0, 1)] + [(1, t) for t in range(p)]:
        solver.add(ev(lhs, vals[x], vals[y]) == ev(rhs, vals[x], vals[y]))
    if latin:
        solver.add(z3.Distinct([op(vals[1], vals[y]) for y in range(p)]))
        solver.add(z3.Distinct([op(vals[x], vals[1]) for x in range(p)]))
        solver.add(op(vals[1], vals[1]) != vals[0])
    # Without --latin, the encoding adds no cancellation hypotheses.
    status = solver.check()
    result = dict(prime=p, law=law, timeout_seconds=seconds,
                  result=str(status), latin=latin, elapsed_seconds=time.monotonic()-started)
    if status == z3.sat:
        model = solver.model()
        table = [model.eval(op(vals[x], vals[y])).as_long()
                 for x in range(p) for y in range(p)]
        for x in range(p):
            for y in range(p):
                valuation = {'x': x, 'y': y}
                assert evaluate(lhs, valuation, table, p) == evaluate(rhs, valuation, table, p)
                assert table[(g*x % p)*p+g*y % p] == g*table[x*p+y] % p
        result['table'] = table
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--latin', action='store_true',
                        help='also impose cancellation and nonzero squaring; use only with proof')
    parser.add_argument('--search', nargs=3, type=int, metavar=('PRIME', 'LAW', 'SECONDS'))
    args = parser.parse_args()
    if args.search:
        print(json.dumps(search(*args.search, latin=args.latin), indent=2))
        return
    data = checked_data()
    if args.write:
        DATA.write_text(json.dumps(data, indent=2)+'\n')
    else:
        assert json.loads(DATA.read_text()) == data
    print('Checked five source tables and all five scalar root lists.')


if __name__ == '__main__':
    main()

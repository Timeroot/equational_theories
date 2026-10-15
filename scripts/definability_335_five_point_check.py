#!/usr/bin/env python3
"""Check the five-point E335 source and its binary-relation invariants.

The Lean module proves the target contradictions directly. Optional --search
replays their discovery in Z3; its UNSAT answers are not proof dependencies.
"""
import argparse
from itertools import product
import json
from pathlib import Path

from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parent.parent


def evaluate(term, values, op):
    if isinstance(term, str):
        return values[term]
    return op(evaluate(term[0], values, op), evaluate(term[1], values, op))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT / 'data/definability_335_five_point.json').read_text())
    equations = load_equations()
    table, n = data['table'], data['order']
    assert n == 5 and len(table) == n and all(len(row) == n for row in table)
    assert all(0 <= v < n for row in table for v in row)
    op = lambda a, b: table[a][b]
    lhs, rhs = equations[data['source'] - 1]
    for x, y in product(range(n), repeat=2):
        values = dict(x=x, y=y)
        assert evaluate(lhs, values, op) == evaluate(rhs, values, op)
    q = [op(x, x) for x in range(n)]
    assert q == data['diagonal']
    for x in range(n):
        for a, b in product({x, q[x]}, repeat=2):
            assert op(a, b) == q[x]
    for constraint in data['constraints']:
        c, d = (divmod(k, n) for k in constraint['cells'])
        relation = {tuple(pair) for pair in constraint['relation']}
        assert (c[0], d[0]) in relation and (c[1], d[1]) in relation
        for (a, b), (u, v) in product(relation, repeat=2):
            assert (op(a, u), op(b, v)) in relation
    for target in data['targets']:
        lhs, rhs = equations[target['law'] - 1]
        for projection in (lambda x, y: x, lambda x, y: y):
            assert evaluate(lhs, dict(x=0, y=1), projection) != evaluate(
                rhs, dict(x=0, y=1), projection)
    assert [x for x in range(n) if q.count(x) > 1] == [2]
    for example in data['surviving_term_examples']:
        def term_op(x, y):
            if 'term' in example:
                return evaluate(example['term'], dict(x=x, y=y), op)
            values = []
            for i, node in enumerate(example['term_dag']):
                if node in ('x', 'y'):
                    values.append(x if node == 'x' else y)
                else:
                    a, b = node
                    assert 0 <= a < i and 0 <= b < i
                    values.append(op(values[a], values[b]))
            return values[example['root']]
        lhs, rhs = equations[example['law'] - 1]
        for x, y in product(range(n), repeat=2):
            values = dict(x=x, y=y)
            assert evaluate(lhs, values, term_op) == evaluate(rhs, values, term_op)
    print('Verified E335, the diagonal clamp, seven compatible relations, and projection exclusions.')
    print('Lean checks all three target contradictions without SAT certificates or native_decide.')
    print('Also verified E3558 and E4290 term operations on this source; it cannot separate those arrows.')
    if args.search:
        import z3
        domain, es = z3.EnumSort('FivePoint335', [f'p{i}' for i in range(n)])
        f = z3.Function('candidate', domain, domain, domain)
        for target in data['targets']:
            solver = z3.Solver()
            solver.set(timeout=10000)
            solver.add(*[f(es[x], es[x]) == es[q[x]] for x in range(n)])
            for i in target['constraints']:
                c = data['constraints'][i]
                values = [f(es[k // n], es[k % n]) for k in c['cells']]
                solver.add(z3.Or(*[z3.And(*[v == es[a] for v, a in zip(values, pair)])
                                   for pair in c['relation']]))
            lhs, rhs = equations[target['law'] - 1]
            for x, y in target['law_instances']:
                values = dict(x=es[x], y=es[y])
                solver.add(evaluate(lhs, values, f) == evaluate(rhs, values, f))
            result = solver.check()
            print(f'E{target["law"]}: {result}')
            assert result == z3.unsat


if __name__ == '__main__':
    main()

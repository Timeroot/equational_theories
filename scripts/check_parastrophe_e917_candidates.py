#!/usr/bin/env python3
"""Check explicit refutations of the E917 image compressions.

The split candidates also require affine offsets and an extension field: tests
on small prime fields alone miss these counterexamples. This script is a
research check; selected counterexamples are separately proved in Lean.
"""
import itertools
import json
from pathlib import Path


def evaluate(term, table, x, z):
    if isinstance(term, int):
        return (x, z)[term]
    return table[evaluate(term[0], table, x, z)][evaluate(term[1], table, x, z)]


def check(candidate):
    spec = candidate['countermodel']
    if 'base' in spec:
        base, p, a, b, phi = (spec[k] for k in ('base', 'p', 'a', 'b', 'phi'))
        n = len(base)*p
        table = [[p*base[x//p][y//p] + (a*(x%p)+b*(y%p)+phi[x//p][y//p]) % p
                  for y in range(n)] for x in range(n)]
    else:
        n, a, b, constant = (spec[k] for k in ('modulus', 'a', 'b', 'constant'))
        table = [[(a*x+b*y+constant) % n for y in range(n)] for x in range(n)]
    assert all(sorted(row) == list(range(n)) for row in table)
    assert all(sorted(table[x][y] for x in range(n)) == list(range(n)) for y in range(n))
    values = [[evaluate(candidate['core_term'], table, x, z) for z in range(n)]
              for x in range(n)]
    assert all(table[y][table[values[x][z]][table[x][y]]] == x
               for x, y, z in itertools.product(range(n), repeat=3))
    core = lambda x: table[table[x][table[x][x]]][x]
    failure = next((('unit', x) for x in range(n) if table[x][core(x)] != x), None)
    if failure is None:
        failure = next((('cross', x, y) for x, y in itertools.product(range(n), repeat=2)
                        if table[y][table[core(x)][table[x][y]]] != x), None)
    assert failure is not None, 'Expected a failure of the image basis'
    return n, failure


def check_split(candidate):
    spec = candidate['countermodel']
    full = [3, [candidate['core_term'], [0, 3]]]
    core = [[0, [0, 0]], 0]
    if 'table' not in spec:
        n, a, b, constant = (spec[k] for k in ('modulus', 'a', 'b', 'constant'))

        def coefficients(term):
            if isinstance(term, int):
                return [int(i == term) for i in range(4)] + [0]
            left, right = map(coefficients, term)
            result = [(a*x+b*y) % n for x, y in zip(left, right)]
            result[-1] = (result[-1]+constant) % n
            return result

        assert coefficients(full) == [1, 0, 0, 0, 0]
        unit = coefficients([0, core])
        assert unit[-1] == spec['unit_at_zero'] != 0
        return n, ('unit', 0, unit[-1])

    table = spec['table']
    n = len(table)

    def evaluate4(term, values):
        if isinstance(term, int):
            return values[term]
        return table[evaluate4(term[0], values)][evaluate4(term[1], values)]

    assert all(evaluate4(full, values) == values[0]
               for values in itertools.product(range(n), repeat=4))
    failed = evaluate4([0, core], [0, 0, 0, 0])
    assert failed == spec['unit_at_zero'] != 0
    return n, ('unit', 0, failed)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root/'data/parastrophes/e917_image_compression_20261103.json').read_text())
    for candidate in data['candidates']:
        if candidate['status'] == 'refuted':
            n, failure = check(candidate)
            print(f"Candidate {candidate['index']}: order {n} satisfies compression but fails the basis at {failure}")
        else:
            print(f"Candidate {candidate['index']}: OPEN (not counted as a characterization)")
    split = json.loads((root/'data/parastrophes/e917_split_compression_20261103.json').read_text())
    for candidate in split['variants']:
        if candidate['status'].startswith('refuted'):
            n, failure = check_split(candidate)
            print(f"Split candidate {candidate['variant']}: order {n} counterexample at {failure}")
        else:
            print(f"Split candidate {candidate['variant']}: OPEN")
    contexts = json.loads((root/'data/parastrophes/e917_unit_iteration_candidate_20261103.json').read_text())
    for candidate in [contexts, *contexts['other_refuted_contexts']]:
        n, failure = check_split(candidate)
        print(f"Unit-iteration candidate ({candidate['operations']} operations): "
              f"order {n} counterexample at {failure}")

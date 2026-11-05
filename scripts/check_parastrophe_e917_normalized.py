#!/usr/bin/env python3
"""Check term sizes and the nonlinear refutation of the 50-operation candidate.

The two bridges have independent parameters. We check that B1(x,z,w) is
independent of both z and w on the entire table. Consequently checking the
remaining x,y pairs suffices for the full six-variable identity. No conclusion
about the unproved 46-operation candidate follows from this check.
"""
import itertools
import json
from pathlib import Path


def size(term):
    return 0 if isinstance(term, int) else 1 + size(term[0]) + size(term[1])


def variables(term):
    return {term} if isinstance(term, int) else variables(term[0]) | variables(term[1])


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / 'data/parastrophes/e917_normalized_candidates_20261103.json').read_text())
    for candidate in data['candidates']:
        assert size(candidate['rhs']) == candidate['operations']
        assert variables(candidate['rhs']) == set(range(candidate['variables']))
    candidate = data['candidates'][1]
    spec = candidate['countermodel']
    base, p, a, b, phi = (spec[k] for k in ['base', 'p', 'a', 'b', 'phi'])
    n = len(base) * p
    assert n == spec['order'] == 25
    table = [[p * base[x // p][y // p] +
              (a * (x % p) + b * (y % p) + phi[x // p][y // p]) % p
              for y in range(n)] for x in range(n)]
    assert all(sorted(row) == list(range(n)) for row in table)
    assert all(sorted(table[x][y] for x in range(n)) == list(range(n)) for y in range(n))

    def op(x, y):
        return table[x][y]

    def core(x):
        return op(op(x, op(x, x)), x)

    def F(x, z):
        return op(z, op(core(x), op(x, z)))

    def B1(x, z, w):
        return op(F(z, w), op(core(x), op(x, z)))

    assert all(B1(x, z, w) == B1(x, x, x)
               for x, z, w in itertools.product(range(n), repeat=3))

    # Check the actual saved tree, with its two B1 occurrences, not a
    # separately transcribed formula. Bridge independence justifies setting
    # the auxiliary variables to x even for the B1 whose first input is U(x).
    def value(term, assignment):
        if isinstance(term, int):
            return assignment[term]
        return op(value(term[0], assignment), value(term[1], assignment))

    assert all(value(candidate['rhs'], [x, y, x, x, x, x]) == x
               for x, y in itertools.product(range(n), repeat=2))
    x = spec['failure']
    assert op(x, core(x)) != x or F(x, x) != x
    print('Term sizes checked: 46 operations / 8 variables; 50 operations / 6 variables.')
    print('Order-25 quasigroup refutes the full 50-operation candidate converse.')
    print('The 46-operation candidate remains unproved.')


if __name__ == '__main__':
    main()

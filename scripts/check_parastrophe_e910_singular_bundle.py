#!/usr/bin/env python3
"""Independently check the saved integer certificate and small reductions.

The Lean theorem proves the construction at every odd prime. These table
checks additionally guard the orientation of the source/division operations.
"""
import json
from pathlib import Path

record = json.loads(Path('data/parastrophes/e910_singular_image_20261105.json').read_text())
q, a, b = (record[k] for k in ('colour', 'left', 'right'))
n = len(q)
assert n == 7
assert all(sorted(row) == list(range(n)) for row in q)
assert all(x in (1, -1, -2) for row in b for x in row)
assert sum(x == -2 for row in b for x in row) == 1
for i in range(n):
    for j in range(n):
        k, ell = q[i][j], q[i][q[i][j]]
        m = q[j][ell]
        assert q[i][m] == i
        assert a[i][m] + b[i][m]*b[j][ell]*(a[i][k] + b[i][k]*a[i][j]) == 1
        assert a[j][ell] + b[j][ell]*b[i][k]*b[i][j] == 0
print('All 49 integer coefficient identities hold')

for p in (2, 3, 5, 7):
    def op(x, y):
        i, u = divmod(x, p)
        j, v = divmod(y, p)
        return p*q[i][j] + (a[i][j]*u + b[i][j]*v) % p

    table = [[op(x, y) for y in range(n*p)] for x in range(n*p)]
    assert all(x == table[x][table[y][table[x][table[x][y]]]]
               for x in range(n*p) for y in range(n*p))
    if p == 2:
        row = p*record['bad_row'][0] + record['bad_row'][1]
        x, y = [p*i + u for i, u in record['collision_inputs']]
        z = p*record['collision_output'][0] + record['collision_output'][1]
        assert x != y and table[row][x] == table[row][y] == z
        print('Order 14: E427 holds and the specified row collision is verified')
    else:
        assert all(sorted(row) == list(range(n*p)) for row in table)
        source = [[row.index(y) for y in range(n*p)] for row in table]
        assert all(x == source[y][source[source[y][x]][source[y][y]]]
                   for x in range(n*p) for y in range(n*p))
        print(f'Order {n*p}: rows bijective, inverse source satisfies E910')

#!/usr/bin/env python3
"""Check the E1483 projector follow-up's finite counterexamples.

This verifies tables and counterexamples directly. The surviving candidate
identities are finite observations only, not general spectrum theorems.
"""
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def lawful(table, number=1483):
    n = len(table)
    assert all(len(row) == n and all(0 <= x < n for x in row) for row in table)
    return all(table[table[y][x]][table[x][table[y][z] if number == 1483 else table[z][y]]] == x
               for x, y, z in product(range(n), repeat=3))


def main():
    data = json.loads((ROOT / 'data/spectrum/1483_projector_followup.json').read_text())
    for record in data['counterexamples']:
        table = record['table']
        assert lawful(table)
        a, b, c, x = (record[k] for k in ('a', 'b', 'c', 'x'))
        p = lambda b, t: table[a][table[t][b]]
        if record['name'] == 'noncommuting':
            lhs, rhs = p(b, p(c, x)), p(c, p(b, x))
        elif record['name'] == 'noncommuting_on_row':
            u = table[a][x]
            assert u == record['row_value']
            lhs, rhs = p(b, p(c, u)), p(c, p(b, u))
        elif record['name'] == 'row_inclusion':
            u, v = x, p(b, x)
            assert u in table[a] and (u, v) == (record['u'], record['v'])
            ru, rv = set(table[u]), set(table[v])
            assert sorted(ru) == record['row_u'] and sorted(rv) == record['row_v']
            assert not rv <= ru
            continue
        else:
            u, v = x, p(b, x)
            assert u in table[a] and (u, v) == (record['u'], record['v'])
            cu = {row[u] for row in table}
            cv = {row[v] for row in table}
            assert sorted(cu) == record['column_u']
            assert sorted(cv) == record['column_v']
            assert not cv <= cu
            continue
        assert (lhs, rhs) == (record['lhs'], record['rhs']) and lhs != rhs

    untwist = data['cubic_untwist_old_order8']
    table = json.loads((ROOT / untwist['source']).read_text())['table']
    phi = untwist['automorphism']
    n = len(table)
    assert lawful(table) and sorted(phi) == list(range(n))
    assert all(phi[phi[phi[x]]] == x for x in range(n))
    assert all(phi[table[x][y]] == table[phi[x]][phi[y]] for x, y in product(range(n), repeat=2))
    new = [[table[phi[x]][phi[phi[y]]] for y in range(n)] for x in range(n)]
    assert lawful(new, 1485)

    # Check the surviving conjectures on the recorded models and their opposites.
    models = [table, data['counterexamples'][0]['table'], data['counterexamples'][1]['table']]
    for original in models:
        for table in (original, list(map(list, zip(*original)))):
            assert lawful(table)
            n = len(table)
            ranks = [len(set(row)) for row in table]
            p = lambda a, b, x: table[a][table[x][b]]
            for a, b, c, x in product(range(n), repeat=4):
                assert p(a, b, p(a, b, x)) == p(a, b, x)
                assert p(a, b, p(a, c, p(a, b, x))) == p(a, c, p(a, b, x))
                if x in table[a] and p(a, b, x) != x:
                    assert ranks[p(a, b, x)] < ranks[x]
    print('Checked 4 counterexamples, the cubic untwist, and candidate identities on 6 finite tables.')


if __name__ == '__main__':
    main()

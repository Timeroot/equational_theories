#!/usr/bin/env python3
"""Exact supplementary calculations for docs/e667_structure_20261004.md.

These are research calculations, not a source of Lean proof assertions.
Uses only the Python standard library. With no arguments, prints JSON.
"""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    return c


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return add(c, [0])


def resultant(a, b):
    """Determinant of the Sylvester matrix, with exact rational elimination."""
    m, n = len(a) - 1, len(b) - 1
    rows = [[0] * i + a[::-1] + [0] * (n - 1 - i) for i in range(n)]
    rows += [[0] * i + b[::-1] + [0] * (m - 1 - i) for i in range(m)]
    rows = [[Fraction(x) for x in row] for row in rows]
    det = Fraction(1)
    for i in range(m + n):
        j = next((j for j in range(i, m + n) if rows[j][i]), None)
        if j is None:
            return 0
        if j != i:
            rows[i], rows[j] = rows[j], rows[i]
            det = -det
        pivot = rows[i][i]
        det *= pivot
        for j in range(i + 1, m + n):
            ratio = rows[j][i] / pivot
            for k in range(i, m + n):
                rows[j][k] -= ratio * rows[i][k]
    assert det.denominator == 1
    return int(det)


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return len(pivots)


def law(q):
    n = len(q)
    return all(q[y][q[x][q[q[x][x]][y]]] == x
               for x in range(n) for y in range(n))


def cocycles(q):
    n = len(q)
    constraints = []
    for i in range(n):
        for j in range(n):
            s = q[i][i]
            t = q[s][j]
            u = q[i][t]
            row = 0
            for a, b in [(i, i), (s, j), (i, t), (j, u)]:
                row ^= 1 << (a * n + b)
            constraints.append(row)
    gauge = []
    for k in range(n):
        row = 0
        for i in range(n):
            for j in range(n):
                if ((i == k) + (j == k) + (q[i][j] == k)) % 2:
                    row |= 1 << (i * n + j)
        assert all((row & c).bit_count() % 2 == 0 for c in constraints)
        gauge.append(row)
    out = {'dimension': n * n - rank(constraints), 'gauge_dimension': rank(gauge)}
    if all(q[i][j] == q[j][i] for i in range(n) for j in range(n)):
        symmetric = constraints + [(1 << (i * n + j)) ^ (1 << (j * n + i))
                                   for i in range(n) for j in range(i)]
        out['commutative_dimension'] = n * n - rank(symmetric)
    return out


def calculations():
    F, G, H = [1, 0, 1], [-1, -1, 0, 1], [1, -1, 0, 1]
    P, K = [-1, 0, 0, 0, -1, 0, -1, 0, 1], [1, 1, 1, 0, 0, -1]
    U, V = [6, 3, 2, -1, -2], [4, -1, -2]
    assert mul(mul(F, G), H) == P
    assert mul([-1], mul(F, G)) == K
    assert add(mul(U, H), mul(V, K)) == [10]
    resultants = [resultant(F, G), resultant(F, H), resultant(G, H)]
    assert list(map(abs, resultants)) == [5, 5, 8]
    table = [[0, 2, 3, 4, 1], [2, 1, 4, 0, 3], [3, 4, 2, 1, 0],
             [4, 0, 1, 3, 2], [1, 3, 0, 2, 4]]
    labels = [0, 1, 3, 4, 2]
    assert law(table)
    for i in range(5):
        for j in range(5):
            assert labels[table[i][j]] == 3 * (labels[i] + labels[j]) % 5
    for i, j in itertools.combinations(range(5), 2):
        closure = {i, j}
        while True:
            new = closure | {table[a][b] for a in closure for b in closure}
            if new == closure:
                break
            closure = new
        assert len(closure) == 5
    source = ROOT / 'data/spectrum/667_small_quotients.json'
    small = json.loads(source.read_text())
    covers = []
    for entry in small['orders']:
        for index, q in enumerate(entry['isomorphism_classes']):
            assert law(q)
            covers.append({'order': len(q), 'class_index': index, **cocycles(q)})
    return {
        'status': 'RESEARCH_CALCULATION_NOT_LEAN',
        'polynomial_coefficients_ascending': dict(F=F, G=G, H=H, P=P, K=K, U=U, V=V),
        'identities_verified': ['F*G*H=P', '-F*G=K', 'U*H+V*K=10'],
        'resultants_FG_FH_GH': resultants,
        'five_point_table': table,
        'five_point_affine_labels': labels,
        'every_distinct_pair_generates_five': True,
        'small_quotients_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'two_fiber_cocycle_spaces': covers,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(calculations(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end='')


if __name__ == '__main__':
    main()

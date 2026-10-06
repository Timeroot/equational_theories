#!/usr/bin/env python3
"""Reconstruct E667 models at 131, 339, and 443 from a 26-point E63 frame.

The Lean proof is Equation63/ProjectiveFrame13.lean. This independent replay
checks the full expanded models, but stores only a compact recipe and hashes.
No model search or trusted external certificate is used in the Lean proof.
"""
import argparse
import hashlib
from itertools import combinations, product
import json
from pathlib import Path

from spectrum_63_bennett import prime, product as table_product
from spectrum_63_idempotent_seeds import PARTIAL8
from spectrum_667_idempotent_search import checked_table

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'data/spectrum/e667_projective_frame.json'

if not __debug__:
    raise RuntimeError('Do not disable assertions when checking model certificates')


def left_division(table):
    return [[row.index(y) for y in range(len(table))] for row in table]


def projective_plane():
    points = [x for x in product(range(3), repeat=3)
              if any(x) and next(a for a in x if a) == 1]
    lines = [[i for i, x in enumerate(points)
              if sum(a*b for a, b in zip(x, v)) % 3 == 0] for v in points]
    assert len(points) == 13 and all(len(line) == 4 for line in lines)
    assert all(sum(x in line and y in line for line in lines) == 1
               for x, y in combinations(range(13), 2))
    return points, lines


def frame():
    _, lines = projective_plane()
    # Values within a hole are unused, and assigned the dummy value zero.
    partial = [[next((z for z in range(8) if PARTIAL8[x][z] == y), 0)
                for y in range(8)] for x in range(8)]
    def op(x, y):
        i, a = divmod(x, 2)
        j, b = divmod(y, 2)
        line = next(line for line in lines if i in line and j in line)
        z = partial[4*a+line.index(i)][4*b+line.index(j)]
        return 2*line[z % 4]+z//4
    table = [[op(x, y) for y in range(26)] for x in range(26)]
    for x, y in product(range(26), repeat=2):
        if x//2 != y//2:
            assert table[y][table[x][table[x][y]]] == x
            assert x//2 != table[x][y]//2
            assert y//2 != table[x][table[x][y]]//2
    return table, partial


def cubic27():
    points = list(product(range(3), repeat=3))
    index = {x: i for i, x in enumerate(points)}
    def op(x, y):
        return ((x[0]+x[2]-y[2]) % 3,
                (x[1]-x[0]-x[2]+y[0]+y[2]) % 3,
                (x[2]-x[1]+y[1]) % 3)
    return [[index[op(x, y)] for y in points] for x in points]


def build(m):
    fillings = {5: lambda: left_division(prime(11)),
                13: cubic27,
                17: lambda: left_division(table_product(prime(5), prime(7)))}
    hole = fillings[m]()
    factor = left_division(prime(m, False))
    base, _ = frame()
    assert len(hole) == 2*m+1
    checked_table(left_division(hole))
    n = 26*m+1
    def op(x, y):
        ix, a = divmod(x-1, 2*m) if x else (None, 0)
        iy, b = divmod(y-1, 2*m) if y else (None, 0)
        if not x or not y or ix == iy:
            group = ix if x else iy
            z = hole[a+1 if x else 0][b+1 if y else 0]
            return 0 if not z else 2*m*group+z
        ah, ac = divmod(a, m)
        bh, bc = divmod(b, m)
        z = base[2*ix+ah][2*iy+bh]
        return 1+m*z+factor[ac][bc]
    table = [[op(x, y) for y in range(n)] for x in range(n)]
    # Checks Latinness, idempotence, E229 after left division, then E63 and E667.
    assert checked_table(left_division(table)) == table
    return table


def manifest():
    points, lines = projective_plane()
    _, partial = frame()
    models = []
    for m in (5, 13, 17):
        table = build(m)
        models.append(dict(order=len(table), factor_order=m, enlarged_hole_order=2*m+1,
                           idempotent=True,
                           table_sha256=hashlib.sha256(json.dumps(
                               table, separators=(',', ':')).encode()).hexdigest()))
    return dict(construction='13-point projective plane, partial C3 frame, product, pointed hole fillings',
                formula='26*m+1 from E63(m) and idempotent E63(2*m+1)',
                status='PROVED_IN_LEAN',
                lean_file='equational_theories/Spectrum/Equation63/ProjectiveFrame13.lean',
                lean_theorem='Spectrum.E63.ProjectiveFrame13.models',
                order339_theorem='Spectrum.E63.ProjectiveFrame13.idem339',
                source='Bennett (1989), Quasigroup Identities and Mendelsohn Designs, Figure 1',
                projective_points=points, projective_lines=lines,
                partial_e63_table=partial, models=models)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    content = json.dumps(manifest(), indent=2)+'\n'
    if args.check:
        assert DEST.read_text() == content, f'Stale manifest: {DEST}'
    else:
        DEST.write_text(content)
    print('Verified full idempotent E63/E667 models at 131, 339, and 443.')

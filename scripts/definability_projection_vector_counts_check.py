#!/usr/bin/env python3
"""Check projection families whose kernel is a product of cyclic groups."""
import argparse
import copy
import itertools
import json
import math
from pathlib import Path

import numpy as np

from definability_counting_upgrades_check import model_indices
from definability_orbit_certificates_check import matrix
from definability_projection_kernel_counts_check import render as kernel_render
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]


def chart(maps, zero=True):
    n = len(maps[0])
    identity = list(range(n))
    assert identity in maps and len({tuple(p) for p in maps}) == len(maps)
    assert all(sorted(p) == identity for p in maps)
    group = {tuple(p) for p in maps}
    assert all(tuple(p[q[x]] for x in range(n)) in group for p in maps for q in maps)
    representatives, choices, stabilizers = [], [], []
    transport = [None] * n
    for x in range(n):
        if transport[x] is not None:
            continue
        i = len(representatives)
        representatives.append(x)
        fixed = [j for j, p in enumerate(maps) if p[x] == x]
        stabilizers.append(fixed)
        choices.append([y for y in range(n) if (not zero or x != 0 or y == 0)
                        and all(maps[j][y] == y for j in fixed)])
        for j, p in enumerate(maps):
            transport[p[x]] = [i, j]
    functions = sorted([[maps[j][values[i]] for i, j in transport]
                        for values in itertools.product(*choices)])
    width = max(map(len, stabilizers))
    return dict(representatives=representatives, choices=choices, transport=transport,
                stabilizers=[s + [maps.index(identity)] * (width - len(s))
                             for s in stabilizers], functions=functions)


def group_table(moduli):
    n = math.prod(moduli)
    radix = np.cumprod([1] + moduli[:-1])
    points = np.arange(n)[:, None] // radix % np.array(moduli)
    return ((points[:, None, :] + points[None, :, :]) % np.array(moduli)) @ radix


def render(d):
    moduli = d['kernel_moduli']
    n = math.prod(moduli)

    def literal(x):
        digits = []
        for modulus in moduli:
            digits.append(str(x % modulus))
            x //= modulus
        return '(' + ', '.join(digits) + ')' if len(digits) > 1 else digits[0]

    def field(i):
        return 'x' if len(moduli) == 1 else 'x' + '.2' * i + ('.1' if i + 1 < len(moduli) else '')

    stub = copy.deepcopy(d)
    stub.update(kernel_modulus=n, kernel_scalars=list(range(len(d['kernel_maps']))))
    stub['kernel_functions'] = [[literal(x) for x in row] for row in d['kernel_functions']]
    stub['unary_chart']['representatives'] = [literal(x) for x in d['unary_chart']['representatives']]
    stub['unary_chart']['choices'] = [[literal(x) for x in row] for row in d['unary_chart']['choices']]
    s = kernel_render(stub)
    group_type = '(' + ' × '.join(f'ZMod {m}' for m in moduli) + ')'
    index = ' + '.join(f'{math.prod(moduli[:i])} * {field(i)}.val' for i in range(len(moduli)))
    s = s.replace(f'abbrev B := ZMod {n}', f'abbrev B := {group_type}\ndef index (x : B) : ℕ := {index}')
    begin, end = s.index('def scalarData'), s.index('def valueData')
    m = len(d['kernel_maps'])
    maps = matrix([[literal(x) for x in row] for row in d['kernel_maps']])
    s = s[:begin] + f'''def mapData : Array (Array B) := {maps}
def mapFunction (i : Fin {m}) (x : B) : B :=
  (mapData.getD i.val #[]).getD (index x) 0
theorem map_zero : ∀ i, mapFunction i 0 = 0 := by native_decide
theorem map_add : ∀ i x y, mapFunction i (x + y) = mapFunction i x + mapFunction i y := by native_decide
def maps (i : Fin {m}) : B →+ B where
  toFun := mapFunction i
  map_zero' := map_zero i
  map_add' := map_add i
''' + s[end:]
    s = s.replace('.getD x.val 0', '.getD (index x) 0')
    s = s.replace('transportData.getD b.val', 'transportData.getD (index b)')
    return s


def check(d, return_models=False):
    a = d['base_modulus']
    GB = group_table(d['kernel_moduli'])
    b = len(GB)
    n = a * b
    assert n == d['order']
    maps = d['kernel_maps']
    for p in map(np.array, maps):
        assert p[0] == 0 and np.array_equal(p[GB], GB[p[:, None], p[None, :]])
    complete = chart(maps)
    fs = complete.pop('functions')
    assert complete == d['unary_chart'] and fs == d['kernel_functions']
    size = (a * len(fs)) ** a
    assert size == d['family_count']
    codes = np.arange(size)
    g, h = np.empty((size, a), dtype=np.uint16), np.empty((size, a), dtype=np.uint16)
    divisor = 1
    for i in range(a):
        g[:, i] = codes // divisor % a
        divisor *= a
    for i in range(a):
        h[:, i] = codes // divisor % len(fs)
        divisor *= len(fs)
    assert divisor == size
    f = g[:, np.arange(n) % a] + a * np.array(fs)[h[:, np.arange(n) % a], np.arange(n) // a]
    assert len({tuple(row) for row in f}) == size
    G = np.array([[(x % a + y % a) % a + a * GB[x // a, y // a]
                   for y in range(n)] for x in range(n)])
    inverse = np.array([next(y for y in range(n) if G[x, y] == 0) for x in range(n)])
    difference = G[inverse[:, None], np.arange(n)[None, :]]
    # This independently enumerates every allowed unary parameter and checks
    # the projection and kernel maps before evaluating every law assignment.
    for p in [np.arange(n) % a] + [np.arange(n) % a + a * np.array(p)[np.arange(n) // a]
                                  for p in maps]:
        assert np.array_equal(p[f], f[:, p])

    class Tables:
        shape = (size, n, n)

        def __len__(self):
            return size

        def __getitem__(self, key):
            i, x, y = key
            return G[x, f[i, difference[x, y]]]

    tables = Tables()
    equations = load_equations()
    models = {law: model_indices(equations, tables, law)
              for law in sorted({e[key] for e in d['candidates'] for key in ['source', 'target']})}
    for e in d['candidates']:
        assert len(models[e['source']]) == e['source_count']
        assert len(models[e['target']]) == e['target_count']
    print(d['namespace'], 'complete family', size, 'full-assignment counts',
          {law: len(indices) for law, indices in models.items()}, flush=True)
    if return_models:
        union = np.unique(np.concatenate(list(models.values())))
        return G[np.arange(n)[None, :, None], f[union][:, difference]].astype(np.uint16)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--only')
    args = parser.parse_args()
    for path in sorted((ROOT / 'data').glob('definability_projection_vector_count*.json')):
        d = json.loads(path.read_text())
        if args.only and args.only not in d['namespace']:
            continue
        check(d)
        target = ROOT / 'equational_theories/Definability/Generated' / (d['namespace'] + '.lean')
        if args.write:
            target.write_text(render(d))
        else:
            assert target.read_text() == render(d)

#!/usr/bin/env python3
"""Regressions for the Lean-proved conditional finite cube constructions.

The theorem is in Definability/CubeConditional.lean; these computations are
independent regressions, not its proof. The default checks saved sources and
their small pair-products. --search reproduces the earlier bounded Z3 probes.
The original construction makes no claim of recoverability. The image-permutation
version in CubeForwardStructural is also checked here, in both directions.
"""
import argparse
import itertools
import json
from pathlib import Path
import time
import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def saved_models():
    models = {}

    def walk(obj, path):
        if isinstance(obj, list):
            n = len(obj)
            if 1 < n < 40 and all(isinstance(row, list) and len(row) == n
                    and all(type(x) is int and 0 <= x < n for x in row)
                    for row in obj):
                models.setdefault(tuple(map(tuple, obj)), str(path.relative_to(ROOT)))
            else:
                for part in obj:
                    walk(part, path)
        elif isinstance(obj, dict):
            for part in obj.values():
                walk(part, path)

    paths = set()
    for pattern in ('definability_*cube*.json', 'definability_*3342*.json',
                    'definability_*recovery*.json',
                    'definability_commutative_obstructions.json',
                    'definability_residual_models.json'):
        paths.update((ROOT / 'data').glob(pattern))
    for path in sorted(paths):
        walk(json.loads(path.read_text()), path)
    return [(np.array(table), path) for table, path in models.items()]


def satisfies(table, law):
    indices = np.arange(len(table))
    square = table[indices, indices]
    twist = table[indices, square] if law == 3342 else table[square, indices]
    return bool(np.all(table == table[:, twist].T))


def candidate(table):
    indices = np.arange(len(table))
    square = table[indices, indices]
    left_cube = table[indices, square]
    return np.where(square[:, None] == square[None, :], table, left_cube[table])


def image_permutation(cube):
    image = np.unique(cube)
    assert set(cube[image]) == set(image)
    permutation = np.arange(len(cube))
    permutation[image] = cube[image]
    assert len(np.unique(permutation)) == len(cube)
    return permutation


def structural_forward(table):
    indices = np.arange(len(table))
    square = table[indices, indices]
    permutation = image_permutation(table[indices, square])
    return np.where(square[:, None] == square[None, :], table, permutation[table])


def structural_reverse(table):
    indices = np.arange(len(table))
    square = table[indices, indices]
    inverse = np.argsort(image_permutation(table[square, indices]))
    return np.where(square[:, None] == square[None, :], table, inverse[table])


def check_structural(table, law):
    forward, backward = ((structural_forward, structural_reverse) if law == 3342
                         else (structural_reverse, structural_forward))
    other = 3545 if law == 3342 else 3342
    target = forward(table)
    assert satisfies(target, other)
    assert np.array_equal(backward(target), table)


def check_saved():
    sources = [(table, path) for table, path in saved_models() if satisfies(table, 3342)]
    for table, path in sources:
        assert satisfies(candidate(table), 3545), (len(table), path)
        check_structural(table, 3342)
    reverse_sources = [table for table, _ in saved_models() if satisfies(table, 3545)]
    for table in reverse_sources:
        check_structural(table, 3545)
    small = [(table, path) for table, path in sources if len(table) < 12]
    count = 0
    for (a, pa), (b, pb) in itertools.combinations_with_replacement(small, 2):
        table = (a[:, None, :, None] * len(b) + b[None, :, None, :]).reshape(
            len(a) * len(b), -1)
        assert satisfies(table, 3342)
        assert satisfies(candidate(table), 3545), (pa, pb)
        check_structural(table, 3342)
        count += 1
    print(f'Candidate passed {len(sources)} saved sources and {count} pair-products.')
    print(f'Reversible version passed those sources/products and '
          f'{len(reverse_sources)} saved E3545 sources, including exact recovery.')


def search(seconds):
    import z3
    for n in range(2, 9):
        carrier, values = z3.EnumSort(f'CubeCandidate{n}', [f'e{n}_{i}' for i in range(n)])
        f = z3.Function(f'f{n}', carrier, carrier, carrier)
        q = lambda x: f(x, x)
        s = lambda x: f(x, q(x))
        g = lambda x, y: z3.If(q(x) == q(y), f(x, y), s(f(x, y)))
        solver = z3.Solver()
        solver.set(timeout=round(seconds * 1000))
        solver.add([f(x, y) == f(y, s(x)) for x in values for y in values])
        a, b = z3.Consts(f'a{n} b{n}', carrier)
        solver.add(g(a, b) != g(b, g(g(a, a), a)))
        start = time.monotonic()
        result = solver.check()
        print(f'Order {n}: {result}; {time.monotonic() - start:.2f}s', flush=True)
        if result == z3.sat:
            model = solver.model()
            index = {str(value): i for i, value in enumerate(values)}
            table = [[index[str(model.eval(f(x, y)))] for y in values] for x in values]
            assert satisfies(np.array(table), 3342)
            assert not satisfies(candidate(np.array(table)), 3545)
            print(json.dumps({'table': table, 'x': index[str(model.eval(a))],
                              'y': index[str(model.eval(b))]}, indent=2))
            break


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', action='store_true')
    parser.add_argument('--seconds', type=float, default=15)
    args = parser.parse_args()
    check_saved()
    if args.search:
        search(args.seconds)

#!/usr/bin/env python3
"""Check successor-family recovery and optionally reproduce triple interpolation.

The family theorems are also proved in Lean. Interpolation remains exploratory:
passing every triple does not establish a common defining or recovery term.
"""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def evaluate(term, table):
    n = len(table)
    if term == 'x':
        return [[x for _ in range(n)] for x in range(n)]
    if term == 'y':
        return [list(range(n)) for _ in range(n)]
    left, right = (evaluate(t, table) for t in term)
    return [[table[left[x][y]][right[x][y]] for y in range(n)] for x in range(n)]


def satisfies(table, equation):
    n = len(table)
    for x in range(n):
        q = table[x][x]
        twist = table[x][q] if equation == 3342 else table[q][x]
        if any(table[x][y] != table[y][twist] for y in range(n)):
            return False
    return True


def family(successor, group, identity, e, equation):
    p = len(group)
    inverse = [next(j for j in range(p) if group[i][j] == identity) for i in range(p)]
    zero = len(successor) * p
    table = [[zero] * (zero + 1) for _ in range(zero + 1)]
    assert all(successor[i] != i and successor[successor[i]] != i
               for i in range(len(successor)))
    assert all(group[e][i] == group[i][e] for i in range(p))
    for x in range(zero):
        i, u = divmod(x, p)
        for y in range(zero):
            j, v = divmod(y, p)
            if i == j:
                table[x][y] = successor[i] * p + identity
            elif successor[i] == j:
                value = group[group[u][inverse[v]]][e]
                if equation == 3545:
                    value = group[value][e]
                table[x][y] = i * p + value
            elif i == successor[j]:
                value = group[v][inverse[u]]
                if equation == 3545:
                    value = group[value][e]
                table[x][y] = j * p + value
    return table


def s3_times_c3():
    permutations = list(itertools.permutations(range(3)))
    elements = list(itertools.product(permutations, range(3)))
    index = {x: i for i, x in enumerate(elements)}
    table = [[index[(tuple(a[b[i]] for i in range(3)), (u + v) % 3)]
              for b, v in elements] for a, u in elements]
    return table, index[((0, 1, 2), 0)], index[((0, 1, 2), 1)]


def check_families():
    data = json.loads((ROOT / 'data/definability_successor_fiber_recovery.json').read_text())
    count = 0
    successors = [[(i + 1) % k for i in range(k)] for k in range(3, 9)]
    successors.append([2, 2, 3, 0])  # Not injective; this is allowed by the theorem.
    groups = [([[(i + j) % p for j in range(p)] for i in range(p)], 0, 1)
              for p in (2, 3, 5, 7)]
    groups.append(s3_times_c3())
    for successor in successors:
        for group, identity, e in groups:
            source = family(successor, group, identity, e, 3342)
            target = family(successor, group, identity, e, 3545)
            assert satisfies(source, 3342)
            assert satisfies(target, 3545)
            assert evaluate(data['forward'], source) == target
            assert evaluate(data['backward'], target) == source
            count += 1
    print(f'{count} successor-family pairs: both laws and both recovery terms checked')

    source = [[0, 0, 1], [0, 0, 1], [1, 1, 2]]
    candidate = json.loads((ROOT / 'data/definability_3342_second_candidate_counterexample.json').read_text())
    target = evaluate(candidate['term'], source)
    assert satisfies(source, 3342) and satisfies(target, 3545)
    assert target == [[0, 0, 0], [0, 0, 0], [0, 0, 2]]
    assert all(target[x][y] in (0, 2) for x in (0, 2) for y in (0, 2))
    assert source[0][2] == 1
    print('42-leaf candidate: three-element closed-subset obstruction to recovery checked')


def check_interpolation(executable):
    data = json.loads((ROOT / 'data/definability_3342_mixed_companions.json').read_text())
    expected = json.loads((ROOT / 'data/definability_cube_focus_checks.json').read_text())
    cases = 0
    with tempfile.TemporaryDirectory(prefix='cube_interpolation_') as directory:
        for pattern, results in expected['triple_interpolation'].items():
            for direction, result in results.items():
                a, b = data['source_tables'], data['target_tables']
                if direction == 'back':
                    a, b = b, a
                blocks = []
                for i in map(int, pattern):
                    blocks += [f'{len(a[i])} {i}',
                               ' '.join(str(x) for row in a[i] for x in row),
                               ' '.join(str(x) for row in b[i] for x in row)]
                src = Path(directory) / 'input.txt'
                out = Path(directory) / 'result.json'
                src.write_text('\n'.join(blocks) + '\n')
                subprocess.run([executable, str(src), str(out)], check=True)
                actual = json.loads(out.read_text())
                assert actual == result, (pattern, direction, actual, result)
                cases += actual['tested']
    assert cases == expected['triple_tests_total'] == 995280
    print(f'{cases:,} triple-interpolation tests reproduced; full recovery remains unproved')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--interpolator', help='compiled definability_cube_interpolation3.cpp')
    args = parser.parse_args()
    check_families()
    if args.interpolator:
        check_interpolation(args.interpolator)

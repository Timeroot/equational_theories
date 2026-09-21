#!/usr/bin/env python3
"""Check the finite data from the spectrum and equivalence-priority pass.

The Lean strict-implication proofs settle two class separations. The rejected
candidate and mixed companions below are research data, not board facts.
"""
import itertools
import json
from pathlib import Path

import numpy as np

from definability_central_candidate_check import evaluate, leaves
from definability_residual_check import lean_array
from definability_table_counts_check import count_models
from definability_twisted_check import satisfies
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]


def generated_subalgebra(table, a, b):
    values = [a] if a == b else [a, b]
    seen = set(values)
    index = 0
    while index < len(values) and len(values) < len(table):
        x = values[index]
        for j in range(index + 1):
            y = values[j]
            for z in (table[x][y], table[y][x]):
                if z not in seen:
                    seen.add(z)
                    values.append(z)
        index += 1
    return frozenset(seen)


def product_table(a, b):
    n, m = len(a), len(b)
    return [[m * a[x // m][y // m] + b[x % m][y % m]
             for y in range(n * m)] for x in range(n * m)]


def main():
    equations = load_equations()
    lean = (ROOT / 'equational_theories/Definability/StrictImplicationSeparations.lean').read_text()
    for source, target, n in [(629, 52, 4), (854, 433, 11)]:
        section = lean.split(f'def source{source} :', 1)[1]
        table = np.array(lean_array(section, 'op :=', f'theorem source{source}_law'))
        assert table.shape == (n, n)
        assert satisfies(equations[source - 1], table)
        assert not satisfies(equations[target - 1], table)
        print(f'E{source} but not E{target}: checked order {n}')

    counts = count_models(equations, [1486], 3)
    assert counts[1486] == 0
    print('E1486: all 19,683 labeled order-three tables excluded')

    candidate = json.loads((ROOT / 'data/definability_3342_second_candidate_counterexample.json').read_text())
    table = np.array(candidate['table'])
    term = candidate['term']
    assert leaves(term) == candidate['leaves'] == 42
    assert satisfies(equations[3341], table)
    x, y = np.indices(table.shape)
    derived = evaluate(term, lambda a, b: table[a, b], x, y)
    u = table[y, x]
    a, b = table[table[x, x], table[y, y]], table[table[y, y], table[x, x]]
    c = table[table[b, u], table[u, b]]
    d = table[a, table[table[table[u, b], b], a]]
    assert np.array_equal(derived, table[table[d, c], c])
    x, y = candidate['witness']
    assert derived[x, y] != derived[y, derived[derived[x, x], x]]
    assert satisfies(equations[3544], table.T)
    text = (ROOT / 'scripts/check_definability_3342_second_candidate.lean').read_text()
    assert lean_array(text, 'op :=', 'def candidate') == table.tolist()
    print('The 42-leaf candidate fails; the opposite operation works on its countermodel')

    data = json.loads((ROOT / 'data/definability_3342_mixed_companions.json').read_text())
    source, target = data['source_tables'], data['target_tables']
    assert all(satisfies(equations[3341], np.array(m)) for m in source)
    assert all(satisfies(equations[3544], np.array(m)) for m in target)
    for i, j in [(0, 0), (1, 1), (0, 1)]:
        a, b = product_table(source[i], source[j]), product_table(target[i], target[j])
        relations = set()
        for x, y in itertools.combinations_with_replacement(range(len(a)), 2):
            r = generated_subalgebra(a, x, y)
            assert r == generated_subalgebra(b, x, y)
            relations.add(r)
        assert len(relations) == data['binary_relations'][f'{i}{j}']['count']
        print(f'Factors {i},{j}: all generated binary relations agree ({len(relations)} distinct)')
    print('No general E3342/E3545 definability claim follows from these companions.')


if __name__ == '__main__':
    main()

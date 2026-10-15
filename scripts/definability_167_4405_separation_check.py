#!/usr/bin/env python3
"""Check the small source and symmetry data for E167 not finite-FO-defining E4405.

The target exclusion is the existing Lean theorem noprn8h4a_Law4405. This
script checks source tables, the numbering change, and automorphisms; it does
not replace that theorem with an external UNSAT claim. --search additionally
reproduces the two short discovery SAT calls using the independent orbit CNF.
"""
from pathlib import Path
from itertools import permutations, product
import argparse
import json


def constructed_operation(x, y, k=2):
    """Four-case E167 construction on F2^k x F2, u=1 and chi(v)=v&1."""
    q = 1 << k
    a, i = x % q, x // q
    b, j = y % q, y // q
    if i == j:
        if a == b:
            return x
        return a + q if i == 0 else b
    if (a ^ b) & 1 == 0:
        return (a ^ i) + q * i
    return (b ^ (1 - i)) + q * j


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', action='store_true')
    args = parser.parse_args()
    data = json.loads(Path('data/definability_167_4405_separation.json').read_text())
    n = 8
    f = data['source']['model']
    g = data['relabeled_model']
    relabel = data['relabeling_to_prn8h4a']
    assert sorted(relabel) == list(range(n))
    for x, y in product(range(n), repeat=2):
        assert g[relabel[x]][relabel[y]] == relabel[f[x][y]]
    for table, generators in [(f, data['generators']), (g, data['prn8h4a_generators'])]:
        assert all(table[table[y][x]][table[x][y]] == x
                   for x, y in product(range(n), repeat=2))
        assert all(s[table[x][y]] == table[s[x]][s[y]]
                   for s in generators for x, y in product(range(n), repeat=2))
    autos = [list(s) for s in permutations(range(n))
             if all(s[g[x][y]] == g[s[x]][s[y]]
                    for x, y in product(range(n), repeat=2))]
    assert autos == data['full_automorphism_group']
    assert len(autos) == 4
    construction = [[constructed_operation(x, y) for y in range(n)] for x in range(n)]
    assert construction == data['explicit_construction_model']
    assert all(construction[construction[y][x]][construction[x][y]] == x
               for x, y in product(range(n), repeat=2))
    assert all(construction[x ^ v][y ^ v] == construction[x][y] ^ v
               for x, y, v in product(range(n), range(n), range(4)))
    print('Verified both E167 tables, relabeling, V4 action, and full source Aut group of order 4.')
    print('Target exclusion: existing Lean theorem noprn8h4a_Law4405; no new certificate.')
    if args.search:
        import definability_167_4405_probe as probe
        probe.W = Path('.cache/e167-4405/separation-recheck')
        probe.W.mkdir(parents=True, exist_ok=True)
        table, count = probe.encoding(n, data['generators'])
        for law, expected in [(167, 'SAT'), (4405, 'UNSAT')]:
            result = probe.solve('V4-two-orbits', n, data['generators'], table, count, law)
            print(law, result['result'], result['seconds'])
            assert result['result'] == expected


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Audit saved E1483 searches without promoting solver reports to Lean proofs.

Check archive hashes, case coverage, and every positive multiplication table.
Logical validity of the exploratory UNSAT reports is not checked here.
"""
import hashlib
import itertools
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]
GROUPS = (
    'minimum_rank_first_pass', 'minimum_rank_long_pass',
    'order12_rank2_profiles', 'order12_rank2_balanced_followup',
    'order12_rank3_prefixes',
)


def main():
    data = json.loads((ROOT / 'data/spectrum/1483_search_followup.json').read_text())
    assert data['equation'] == 1483 and data['order12_status'] == 'UNKNOWN'
    with tarfile.open(ROOT / data['source_archive'], 'r:gz') as archive:
        assert set(archive.getnames()) == set(data['source_sha256'])
        for name, digest in data['source_sha256'].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest() == digest
        for group in GROUPS:
            for record in data[group]:
                saved = json.loads(archive.extractfile(record['recorded_file']).read())
                assert saved == {k: v for k, v in record.items() if k != 'recorded_file'}

    positives = 0
    for group in GROUPS:
        for record in data[group]:
            assert record['status'] in ('sat', 'unsat', 'unknown')
            assert record['seconds'] > 0 and record['budget'] > 0
            if record['status'] != 'sat':
                assert record['table'] is None
                continue
            table, n = record['table'], record['order']
            assert len(table) == n
            assert all(len(row) == n and all(0 <= x < n for x in row) for row in table)
            assert all(table[table[y][x]][table[x][table[y][z]]] == x
                       for x, y, z in itertools.product(range(n), repeat=3))
            ranks = [len(set(row)) for row in table]
            assert min(ranks) == ranks[0] == record['minimum_rank']
            if 'first_row' in record:
                assert table[0] == record['first_row']
            if 'first_row_prefix' in record:
                prefix = record['first_row_prefix']
                assert table[0][:len(prefix)] == prefix
            positives += 1

    profiles = data['order12_rank2_profiles']
    expected = set(itertools.product((1, 2), (1, 2), range(10)))
    assert len(profiles) == 40 and {tuple(r['case']) for r in profiles} == expected
    followups = {tuple(r['case']): r for r in data['order12_rank2_balanced_followup']}
    assert len(followups) == 4
    assert set(followups) == {tuple(r['case']) for r in profiles if r['status'] == 'unknown'}
    for record in profiles:
        a, b, c = record['case']
        row = [1, a, b] + [1] * c + [2] * (9 - c)
        assert record['order'] == 12 and record['minimum_rank'] == 2
        assert record['first_row'] == row
        final = followups.get(tuple(record['case']), record)
        assert final['status'] == 'unsat' and final['first_row'] == row
        if final is not record:
            assert row.count(1) == row.count(2) == 6
            assert final['constraints'] == 'collisions'

    first = {(r['order'], r['minimum_rank']): r for r in data['minimum_rank_first_pass']}
    assert all(first[12, rank]['status'] == 'unsat' for rank in range(6, 12))
    long = data['minimum_rank_long_pass']
    assert len(long) == 4 and {r['minimum_rank'] for r in long} == {2, 3, 4, 5}
    prefixes = data['order12_rank3_prefixes']
    expected = set(itertools.product((1, 2), (1, 2, 3), (1, 2, 3)))
    assert len(prefixes) == 18 and {tuple(r['case']) for r in prefixes} == expected
    for record in prefixes:
        assert record['order'] == 12 and record['minimum_rank'] == 3
        assert record['first_row_prefix'] == [1] + record['case']
    print(f'Checked archive hashes, complete search partitions, and {positives} positive table(s).')
    print('Order 12 remains unknown. Its rank-2 exclusion is external search evidence only.')


if __name__ == '__main__':
    main()

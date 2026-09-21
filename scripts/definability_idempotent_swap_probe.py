#!/usr/bin/env python3
"""Check the square-column-swap candidate for E8 -> E3 on all order-three tables.

This tests one proposed construction, not the full FO-structural arrow.
The default checks the saved report; --write regenerates it.
"""

import argparse
import itertools
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--write", action="store_true")
args = parser.parse_args()
n = 3
permutations = list(itertools.permutations(range(n)))


def automorphisms(table):
    return [
        p
        for p in permutations
        if all(p[table[x][y]] == table[p[x]][p[y]] for x in range(n) for y in range(n))
    ]


count = 0
failures = []
for flat in itertools.product(range(n), repeat=n * n):
    source = [flat[n * i : n * (i + 1)] for i in range(n)]
    if not all(source[x][source[x][x]] == x for x in range(n)):
        continue
    count += 1
    candidate = [
        [
            source[x][source[x][x] if y == x else x if y == source[x][x] else y]
            for y in range(n)
        ]
        for x in range(n)
    ]
    assert all(candidate[x][x] == x for x in range(n))
    sa, ca = automorphisms(source), automorphisms(candidate)
    assert set(sa) <= set(ca)
    if sa != ca:
        failures.append(
            dict(source=source, candidate=candidate, source_auts=sa, candidate_auts=ca)
        )
assert count == 3375 and len(failures) == 278
result = dict(
    order=n, tested_sources=count, failures=len(failures), example=failures[0]
)
path = Path("data/definability_idempotent_swap_probe.json")
content = json.dumps(result, indent=2) + "\n"
if args.write:
    path.write_text(content)
else:
    assert path.read_text() == content, "Stale square-swap probe report."
print(
    f"Checked {count} E8 tables; square-column-swap gains extra automorphisms on {len(failures)}."
)

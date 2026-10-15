#!/usr/bin/env python3
"""Independently check the small E14 research examples; no SAT solver needed."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "data/definability/e14_3272/research_examples.json").read_text())
for example in data["examples"]:
    n, table = example["order"], example["table"]
    assert len(table) == n and all(len(row) == n for row in table)
    assert all(0 <= value < n for row in table for value in row)
    assert all(table[y][table[x][y]] == x for x in range(n) for y in range(n))
    square = [table[x][x] for x in range(n)]
    assert square == example["squares"]
    periodic = []
    for x in range(n):
        seen, y = set(), x
        while y not in seen:
            seen.add(y)
            y = square[y]
        if y == x:
            periodic.append(x)
    assert periodic == example["periodic_points"]
    commutative = all(table[x][y] == table[y][x] for x in range(n) for y in range(n))
    assert commutative == example["commutative"]
    if commutative:
        assert all(square.count(x) % 2 == n % 2 for x in range(n))
    if "nonclosure_pair" in example:
        x, y = example["nonclosure_pair"]
        assert x in periodic and y in periodic
        assert table[x][y] == example["nonclosure_value"]
        assert table[x][y] not in periodic
    if len(set(square)) == n:
        inverse = [square.index(x) for x in range(n)]
        q = [[inverse[table[x][square[y]]] for y in range(n)] for x in range(n)]
        assert all(q[x][x] == q[y][q[x][q[y][y]]] for x in range(n) for y in range(n))
        assert all(square[q[x][inverse[y]]] == table[x][y] for x in range(n) for y in range(n))
    if "generators" in example:
        for g in example["generators"]:
            assert sorted(g) == list(range(n))
            assert all(g[table[x][y]] == table[g[x]][g[y]] for x in range(n) for y in range(n))
    if "e3272_target" in example:
        target = example["e3272_target"]
        assert all(target[x][x] == x for x in range(n))
        assert all(target[x][x] == target[y][target[x][target[y][y]]]
                   for x in range(n) for y in range(n))
        for g in example["generators"]:
            assert all(g[target[x][y]] == target[g[x]][g[y]] for x in range(n) for y in range(n))
    print(f"Checked {example['name']}: E14, diagonal, periodic points, and stated properties")

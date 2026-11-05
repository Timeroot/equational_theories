#!/usr/bin/env python3
"""Replay the E1518 additive extensions and the rejected recovery term.

This is an independent research-data check, not a Lean proof certificate.
The general extension theorem and the first 45-element lift are also in Lean.
The offset equations avoid constructing the final 1215-by-1215 table.
"""

import json
from pathlib import Path


def square_cycles(op, order):
    unseen = set(range(order))
    cycles = []
    while unseen:
        first = min(unseen)
        cycle, x = [], first
        while x in unseen:
            unseen.remove(x)
            cycle.append(x)
            x = op(x, x)
        assert x == first, "Squaring is not a permutation"
        cycles.append(cycle)
    return cycles


def evaluate(term, op, x):
    if term == 0:
        return x
    assert isinstance(term, list) and len(term) == 2
    return op(evaluate(term[0], op, x), evaluate(term[1], op, x))


def main():
    root = Path(__file__).resolve().parents[1]
    path = root / "data/parastrophes/e1518_square_cycles_20261103.json"
    data = json.loads(path.read_text())
    base = data["seed"]["table"]
    n = len(base)
    assert all(sorted(row) == list(range(n)) for row in base)
    assert all(base[base[y][y]][base[x][base[y][x]]] == x
               for x in range(n) for y in range(n))
    assert sorted(map(len, square_cycles(lambda x, y: base[x][y], n))) == [3, 12]
    for index, lift in enumerate(data["lifts"]):
        assert lift["base_order"] == n
        p = lift["modulus"]
        offsets = [[int(c) for c in row] for row in lift["offset_rows"]]
        assert len(offsets) == n
        assert all(len(row) == n and all(0 <= c < p for c in row)
                   for row in offsets)
        assert all((offsets[y][x] + offsets[x][base[y][x]] +
                    offsets[base[y][y]][base[x][base[y][x]]]) % p == 0
                   for x in range(n) for y in range(n))

        def op(x, y):
            i, u = divmod(x, p)
            j, v = divmod(y, p)
            return p * base[i][j] + (v + offsets[i][j]) % p

        order = n * p
        assert lift["lifted_order"] == order
        cycles = square_cycles(op, order)
        longest = max(map(len, cycles))
        if "lifted_cycle_length" in lift:
            assert longest == lift["lifted_cycle_length"]
        if "candidate_failure_input" in lift:
            i, u = lift["candidate_failure_input"]
            x = p * i + u
            term = data["inverse_square_candidate"]["term"]
            value = op(x, evaluate(term, op, x))
            assert value == p * i + (u + lift["candidate_defect"]) % p
            assert value != x
            print(f"Order {order}: candidate fails at {x}, giving {value}.")
        print(f"Order {order}: {n*n} offset equations checked; "
              f"longest square cycle {longest}.")
        if index + 1 < len(data["lifts"]):
            # Only materialize a table when the next level uses it as its base.
            base = [[op(x, y) for y in range(order)] for x in range(order)]
            n = order


if __name__ == "__main__":
    main()

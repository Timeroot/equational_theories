#!/usr/bin/env python3
"""Independently replay the saved candidate-term refutations.

These are research checks, not Lean proofs or catalogue results. They disprove
only the explicitly specified terms, never the existence of a different term.
"""

import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def check(record):
    if "table" in record:
        table = record["table"]
    else:
        base, p, a, b, phi = (record[k] for k in ("base", "p", "a", "b", "phi"))
        n = len(base) * p
        table = [[p * base[x // p][y // p]
                  + (a * (x % p) + b * (y % p) + phi[x // p][y // p]) % p
                  for y in range(n)] for x in range(n)]
    n = len(table)
    assert n == record["order"]
    assert all(sorted(row) == list(range(n)) for row in table)
    assert all(sorted(table[x][y] for x in range(n)) == list(range(n))
               for y in range(n))
    assert satisfies(*load_equations()[record["source"] - 1], sum(table, []), n)
    if "source_square_failure" in record:
        a, b = record["source_square_failure"]
        value = table[a][b]
        assert table[value][value] != table[table[a][a]][table[b][b]]

    if record["side"] == "left":
        division = [[row.index(y) for y in range(n)] for row in table]
    else:
        assert record["side"] == "right"
        division = [[next(z for z in range(n) if table[z][y] == x)
                     for y in range(n)] for x in range(n)]

    def evaluate(term, x, y):
        if isinstance(term, int):
            assert term in (0, 1)
            return x if term == 0 else y
        return division[evaluate(term[0], x, y)][evaluate(term[1], x, y)]

    x, y = record["failed_inputs"]
    value = evaluate(record["term"], x, y)
    test = record["test"]
    if test == "inverse_square":
        assert table[value][value] != x
    elif test == "identity":
        assert value != x
    else:
        assert test == "inverse_multiplication"
        assert value != table[x][y]
    return n


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1] / "data/parastrophes"
    for path in sorted(root.glob("image_candidate_refutations_*.json")):
        for record in json.loads(path.read_text())["records"]:
            n = check(record)
            print(f"E{record['source']} {record['side']}: {record['test']} refuted at order {n}")

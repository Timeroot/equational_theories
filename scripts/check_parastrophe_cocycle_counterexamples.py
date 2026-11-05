#!/usr/bin/env python3
"""Replay the compact image-term counterexamples saved in November 2026.

This is an independent finite-table check, not a Lean proof or an exporter.
The data refutes specified inverse terms, not arbitrary possible terms.
"""

import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def check(record):
    base, p, a, b, phi = (record[k] for k in ("base", "p", "a", "b", "phi"))
    n = len(base) * p
    table = [
        [p * base[x // p][y // p]
         + (a * (x % p) + b * (y % p) + phi[x // p][y // p]) % p
         for y in range(n)]
        for x in range(n)
    ]
    assert all(sorted(row) == list(range(n)) for row in table)
    assert satisfies(*load_equations()[record["source"] - 1], sum(table, []), n)
    division = [[row.index(y) for y in range(n)] for row in table]

    def evaluate(term, x, y, operation):
        if isinstance(term, (int, str)):
            return x if term in (0, "x") else y
        return operation[evaluate(term[0], x, y, operation)][evaluate(term[1], x, y, operation)]

    if "failed_inputs" in record:
        x, y = record["failed_inputs"]
    else:
        x = y = record["failed_input"]
    if "lhs" in record:
        lhs_operation = division if record["division_lhs"] else table
        assert evaluate(record["lhs"], x, y, lhs_operation) != evaluate(record["rhs"], x, y, table)
    else:
        expected = table[x][x] if record["test"] == "square" else table[x][y]
        assert evaluate(record["term"], x, y, division) != expected
    return n, (x, y)


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1] / "data/parastrophes"
    for path in sorted(root.glob("image_cocycle_counterexamples_*.json")):
        for record in json.loads(path.read_text())["records"]:
            n, inputs = check(record)
            print(f"E{record['source']}: order {n}, {record['test']} identity refuted at {inputs}")

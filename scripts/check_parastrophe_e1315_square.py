#!/usr/bin/env python3
"""Replay the saved E1315 source-square recovery counterexamples.

These are research checks, not Lean proofs. A failed candidate does not exclude
other terms or a single-equation characterization of the division image.
"""
import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def main():
    path = Path(__file__).resolve().parents[1] / (
        "data/parastrophes/e1315_square_counterexample_20261104.json")
    data = json.loads(path.read_text())
    tables = data["sources"]["1315"]["tables"]
    divisions = []
    for table in tables:
        n = len(table)
        assert n == 8
        assert all(sorted(row) == list(range(n)) for row in table)
        assert satisfies(*load_equations()[1314], sum(table, []), n)
        division = [[row.index(y) for y in range(n)] for row in table]
        assert all(table[x][division[x][y]] == y and
                   division[x][table[x][y]] == y
                   for x in range(n) for y in range(n))
        divisions.append(division)

    for record in data["refutations"]:
        i, x = record["table_index"], record["input"]

        def evaluate(term):
            if isinstance(term, int):
                assert term == 0
                return x, 0
            left, lc = evaluate(term[0])
            right, rc = evaluate(term[1])
            return divisions[i][left][right], lc + rc + 1

        value, size = evaluate(record["term"])
        assert size == record["operations"]
        assert value == record["candidate_value"]
        assert tables[i][x][x] == record["source_square"] != value
    print(f"Verified {len(tables)} E1315 sources and {len(data['refutations'])} failed terms.")


if __name__ == "__main__":
    main()

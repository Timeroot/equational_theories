#!/usr/bin/env python3
"""Replay the E477 inverse-core research counterexamples, without a solver."""
import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def check(path):
    data = json.loads(path.read_text())
    equation = load_equations()[476]
    tables = data["sources"]["477"]["tables"]
    for source in tables:
        n = len(source)
        assert all(sorted(row) == list(range(n)) for row in source)
        assert satisfies(*equation, [v for row in source for v in row], n)

    for record in data["records"]:
        source = record["source"]
        assert source in tables
        n = len(source)
        division = [[row.index(y) for y in range(n)] for row in source]
        core = [division[x][division[x][x]] for x in range(n)]
        assert sorted(core) == list(range(n))

        def evaluate(term, x):
            if term == 0:
                return x
            assert isinstance(term, list) and len(term) == 2
            return division[evaluate(term[0], x)][evaluate(term[1], x)]

        def size(term):
            return 0 if term == 0 else 1 + size(term[0]) + size(term[1])

        term = record["candidate"]["term"]
        assert size(term) == record["candidate"]["operations"]
        failures = [x for x in range(n) if core[evaluate(term, x)] != x]
        assert failures and failures == record["failed_inputs"]
    return len(data["records"]), len(tables)


def main():
    root = Path(__file__).resolve().parents[1]
    paths = sorted((root / "data/parastrophes").glob("e477_core_inverse_candidates_*.json"))
    assert paths, "No inverse-core records found"
    counts = [check(path) for path in paths]
    print(f"Checked {sum(n for n, _ in counts)} refutations and "
          f"{sum(n for _, n in counts)} E477 source tables in {len(paths)} files.")


if __name__ == "__main__":
    main()

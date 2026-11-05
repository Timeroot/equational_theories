#!/usr/bin/env python3
"""Replay the explicit refutations from the E872 injective-frame search.

Passing the stored tests does not establish a characterization. The main
candidate's forward direction and cancellation lemmas are separately in Lean.
This script checks the stated counterexamples using their complete tables.
"""
import json
from pathlib import Path

from parastrophe_e872_compression import Model, core, right_depth, size
from parastrophe_rewrite_replay import freeze


def matrix_table(record):
    p, a, b, c = (record[k] for k in ("p", "A", "B", "offset"))
    vectors = [(i, j) for i in range(p) for j in range(p)]
    return [[
        p * ((sum(a[0][i] * x[i] + b[0][i] * y[i] for i in range(2)) + c[0]) % p)
        + (sum(a[1][i] * x[i] + b[1][i] * y[i] for i in range(2)) + c[1]) % p
        for y in vectors] for x in vectors]


def main():
    root = Path(__file__).resolve().parents[1]
    record = json.loads((root / "data/parastrophes/e872_injective_candidates_20261104.json").read_text())
    earlier = record["earlier_refuted20"]
    model = Model(earlier["table"])
    assert model.holds(freeze(earlier["term"])) and not model.is_image()

    refuted = {r["index"]: freeze(r["term"]) for r in record["matrix_refuted_terms"]}
    checked = set()
    for witness in record["matrix_counterexamples"]:
        model = Model(matrix_table(witness))
        assert not model.is_image()
        assert all(len(set(row)) == len(row) for row in model.table)
        for index in witness["refuted_candidates"]:
            assert model.holds(refuted[index])
            checked.add(index)
    assert checked == set(refuted)

    # Check that the principal saved syntax is the one used in the Lean module.
    def unit(t):
        return (t, core(t))

    a = (2, 0)
    adjusted = (a, ((a, a), unit(a)))
    bridge = (1, (core(2), (unit(1), 2)))
    term = (adjusted, (bridge, a))
    assert term == freeze(record["main_candidate"]["term"])
    assert size(term) == 28 and right_depth(term) == 3

    principal = record["main_candidate_counterexample"]
    bad = Model(principal["table"])
    assert len(bad.table) == principal["order"] == 6
    assert all(sorted(row) == list(range(6)) for row in bad.table)
    assert bad.holds(term) and not bad.is_image()
    assert bad.table[0][bad.table[0][bad.table[bad.table[0][0]][0]]] == 4

    # These are additional tests, not a proof of the surviving candidates.
    for candidate in record["remaining_candidates"]:
        term = freeze(candidate["term"])
        assert not bad.holds(term)
        assert not Model(earlier["table"]).holds(term)
        for witness in record["matrix_counterexamples"]:
            assert not Model(matrix_table(witness)).holds(term)
    print(f"Checked the 20-operation refutation and {len(checked)} matrix refutations.")
    print("Checked the six-element refutation of the main 28-operation candidate.")
    print(f"{len(record['remaining_candidates'])} candidates remain open; no catalogue row closes.")


if __name__ == "__main__":
    main()

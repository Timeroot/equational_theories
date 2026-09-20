#!/usr/bin/env python3
"""Replay the proposed E3352 → E4408 term-structural obstruction.

This is solver evidence, not a Lean proof or a new board fact. The finite source
and every necessary constraint are checked independently before calling Z3.
The missing formal obligation is the final finite coverage/refutation step.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np
import z3

from definability_residual_check import unary_closure
from definability_twisted_check import satisfies
from spectrum_generate import load_equations


ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data/definability_unary_recovery_3352.json"


def check(seconds: int) -> str:
    data = json.loads(DATA.read_text())
    table = np.array(data["table"], dtype=np.int32)
    n = len(table)
    assert (data["source"], data["target"], n) == (3352, 4408, 8)
    assert data["forward"] == 0 and data["exact_idempotents"]
    assert satisfies(load_equations()[3351], table)
    source_unary = {tuple(u) for u in unary_closure(table)}
    assert source_unary == {tuple(u) for u in data["unary"]}

    # Each forward restriction comes from a source-closed relation containing
    # both projections of its selected input cells. Every binary term therefore
    # obeys it, irrespective of the term's size.
    for cells, rows in data["constraints"]:
        relation = {tuple(row) for row in rows}
        assert all(len(row) == len(cells) for row in rows)
        assert tuple(cell // n for cell in cells) in relation
        assert tuple(cell % n for cell in cells) in relation
        for a, b in itertools.product(rows, repeat=2):
            assert tuple(table[a, b]) in relation

    # If a target keeps one of these families closed, all its unary terms stay
    # there. Since the source breaks that closure, it cannot be recovered by
    # a binary term in the target operation.
    identity = tuple(range(n))
    for rows in data["reverse"]:
        relation = {tuple(row) for row in rows}
        assert identity in relation and relation < source_unary
        assert any(tuple(table[a, b]) not in relation
                   for a, b in itertools.product(rows, repeat=2))

    sort, elements = z3.EnumSort("RecoveryCarrier", [f"e{i}" for i in range(n)])
    operation = z3.Function("candidate", sort, sort, sort)
    solver = z3.Solver()
    solver.set(timeout=seconds * 1000)

    def member(values, rows):
        return z3.Or([z3.And([value == elements[int(entry)]
                             for value, entry in zip(values, row)]) for row in rows])

    for x, y in itertools.product(elements, repeat=2):
        solver.add(operation(x, operation(x, y)) == operation(operation(y, y), x))
    # Mutual term definitions preserve the exact idempotent set in both
    # directions, not merely the source idempotents in the forward direction.
    for i, x in enumerate(elements):
        solver.add((operation(x, x) == x) == bool(table[i, i] == i))
    for cells, rows in data["constraints"]:
        values = [operation(elements[cell // n], elements[cell % n]) for cell in cells]
        solver.add(member(values, rows))
    for rows in data["reverse"]:
        solver.add(z3.Or([
            z3.Not(member([operation(elements[x], elements[y]) for x, y in zip(a, b)],
                          rows))
            for a, b in itertools.product(rows, repeat=2)
        ]))
    result = str(solver.check())
    print(f"Verified source and {len(data['constraints'])} forward restrictions; "
          f"reverse family sizes {[len(r) for r in data['reverse']]}")
    print(f"Z3: {result}")
    if result == "sat":
        raise RuntimeError("the saved proposed obstruction no longer refutes the constraints")
    print("Lean coverage proof pending. The definability board is unchanged.")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=int, default=120, help="Z3 time limit")
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error("--seconds must be positive")
    check(args.seconds)


if __name__ == "__main__":
    main()

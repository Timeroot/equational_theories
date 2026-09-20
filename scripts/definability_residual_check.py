#!/usr/bin/env python3
"""Recompute the rejected candidate families from the residual model bank.

These checks exclude particular forms of defining terms. They do not establish
a negative cell of the definability table. The companion Lean files certify
the exclusions without trusting this program or an external solver.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
from pathlib import Path

import numpy as np

from definability_twisted_check import satisfies
from definability_central_candidate_check import evaluate, leaves
from spectrum_generate import load_equations


ROOT = Path(__file__).resolve().parent.parent
MODEL_PATH = ROOT / "data/definability_residual_models.json"
SQUARE_CERT = ROOT / "scripts/check_definability_square_candidates.lean"
UNARY_CERT = ROOT / "scripts/check_definability_unary_candidates.lean"


def lean_array(text: str, start: str, end: str) -> list:
    """Read one explicitly delimited array literal, not arbitrary Lean syntax."""
    body = text.split(start, 1)[1].split(end, 1)[0].strip()
    assert re.fullmatch(r"[!\[\],\s\d]+", body), "unexpected certificate literal"
    return json.loads(body.replace("!", ""))


def square_powers(table: np.ndarray) -> tuple[list[np.ndarray], int]:
    square = table.diagonal()
    powers = [np.arange(len(table), dtype=np.int32)]
    positions = {tuple(powers[0]): 0}
    while True:
        value = square[powers[-1]]
        key = tuple(value)
        if key in positions:
            return powers, positions[key]
        positions[key] = len(powers)
        powers.append(value)


def unary_closure(table: np.ndarray) -> list[np.ndarray]:
    """Exact closure of the identity under pointwise source multiplication."""
    operations = [np.arange(len(table), dtype=np.int32)]
    seen = {tuple(operations[0])}
    frontier = [0]
    while frontier:
        previous = np.array(operations)
        new = []
        for index in frontier:
            for values in (
                table[operations[index], previous],
                table[previous, operations[index]],
            ):
                for value in values:
                    key = tuple(value)
                    if key not in seen:
                        seen.add(key)
                        new.append(len(operations))
                        operations.append(value)
        frontier = new
    return operations


def check() -> dict:
    equations = load_equations()
    models = json.loads(MODEL_PATH.read_text())
    square_text = SQUARE_CERT.read_text()
    summary = {"square_families": [], "definability_cells_settled": 0}
    for entry in models["square_families"]:
        source, target = entry["source"], entry["target"]
        table = np.array(entry["table"], dtype=np.int32)
        assert satisfies(equations[source - 1], table)
        section = square_text.split(f"namespace E{source}", 1)[1]
        assert lean_array(section, "op :=", "theorem source_law") == entry["table"]
        powers, repeat = square_powers(table)
        checked = 0
        for a, b, c in itertools.product(powers, repeat=3):
            derived = a[table[b[:, None], c[None, :]]]
            assert not satisfies(equations[target - 1], derived)
            checked += 1
        summary["square_families"].append(
            {
                "source": source,
                "target": target,
                "order": len(table),
                "distinct_square_powers": len(powers),
                "repeat_index": repeat,
                "finite_cases": checked,
            }
        )

    entry = models["unary_postprocessor"]
    table = np.array(entry["table"], dtype=np.int32)
    assert satisfies(equations[entry["source"] - 1], table)
    operations = unary_closure(table)
    assert len(operations) == 32
    assert all(
        not satisfies(equations[entry["target"] - 1], u[table]) for u in operations
    )

    unary_text = UNARY_CERT.read_text()
    assert lean_array(unary_text, "op :=", "theorem source_law") == entry["table"]
    certified = lean_array(
        unary_text, "def unary : Fin 32 → Fin 8 → Fin 8 :=", "def combine"
    )
    assert {tuple(u) for u in certified} == {tuple(u) for u in operations}
    assert len({tuple(u) for u in certified}) == 32
    combine = lean_array(
        unary_text, "def combine : Fin 32 → Fin 32 → Fin 32 :=", "theorem identity_mem"
    )
    for i, j in itertools.product(range(32), repeat=2):
        actual = table[np.array(certified[i]), np.array(certified[j])]
        assert actual.tolist() == certified[combine[i][j]]
    summary["unary_postprocessor"] = {
        "source": entry["source"],
        "target": entry["target"],
        "order": len(table),
        "unary_term_operations": len(operations),
        "successful_postprocessors": 0,
    }
    commutative = json.loads(
        (ROOT / "data/definability_commutative_obstructions.json").read_text()
    )
    commutative_text = (
        ROOT / "scripts/check_definability_commutative_obstruction.lean"
    ).read_text()
    flip = np.array([1, 0, 3, 2, 5, 4, 7, 6])
    assert np.all(flip != np.arange(8))
    summary["commutative_terms"] = []
    for source in (3342, 3545):
        table = np.array(commutative[str(source)], dtype=np.int32)
        assert table.shape == (8, 8)
        assert satisfies(equations[source - 1], table)
        assert np.array_equal(table[np.ix_(flip, flip)], flip[table])
        text = commutative_text.split(f"def source{source} :", 1)[1]
        certified = lean_array(text, "op x y := (", " : Fin 8 → Fin 8 → Fin 8)")
        assert certified == table.tolist()
        summary["commutative_terms"].append(
            {"source": source, "order": 8, "fixed_points_of_automorphism": 0}
        )
    adjacency = json.loads(
        (ROOT / "data/definability_1483_adjacency_counterexample.json").read_text()
    )
    table = np.array(adjacency["table"], dtype=np.int32)
    assert table.shape == (9, 9)
    assert adjacency["source"] == 1483
    for equation in (167, 168, 1483):
        assert satisfies(equations[equation - 1], table)
    assert (
        np.flatnonzero(table.diagonal() == np.arange(9)).tolist()
        == adjacency["idempotents"]
    )

    def adjacent(x: int, y: int) -> bool:
        xy, yx = table[x, y], table[y, x]
        return bool(table[xy, xy] == yx and table[yx, yx] == xy)

    assert all(adjacent(*pair) for pair in adjacency["adjacent_pairs"])
    assert not adjacent(*adjacency["nonadjacent_pair"])
    adjacency_text = (
        ROOT / "scripts/check_definability_1483_adjacency.lean"
    ).read_text()
    assert (
        lean_array(adjacency_text, "op x y := (", " : Fin 9 → Fin 9 → Fin 9)")
        == table.tolist()
    )
    summary["idempotent_adjacency"] = {
        "source": 1483,
        "order": 9,
        "transitive": False,
        "stronger_equations": [167, 168],
    }
    candidate = json.loads(
        (ROOT / "data/definability_3342_candidate_counterexample.json").read_text()
    )
    assert (candidate["source"], candidate["target"]) == (3342, 3545)
    table = np.array(candidate["table"], dtype=np.int32)
    assert satisfies(equations[3341], table)
    assert leaves(candidate["term"]) == 22
    x, y = np.indices(table.shape)
    derived = evaluate(candidate["term"], lambda a, b: table[a, b], x, y)
    assert not satisfies(equations[3544], derived)
    x, y = candidate["witness"]
    assert derived[x, y] != derived[y, derived[derived[x, x], x]]
    assert satisfies(equations[3544], table.T)
    certificate = (ROOT / "scripts/check_definability_3342_candidate.lean").read_text()
    assert (
        lean_array(certificate, "op x y := (", " : Fin 8 → Fin 8 → Fin 8)")
        == table.tolist()
    )
    summary["candidate_counterexample"] = {
        "source": 3342,
        "target": 3545,
        "leaves": 22,
        "order": 8,
        "witness": [x, y],
        "opposite_satisfies_target": True,
    }
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="print the exact check summary"
    )
    args = parser.parse_args()
    result = check()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for item in result["square_families"]:
            print(
                f"E{item['source']} → E{item['target']}: "
                f"all square-iteration terms rejected by order {item['order']} "
                f"({item['finite_cases']} finite cases)"
            )
        print("E3352 → E4408: all 32 unary postprocessors rejected by order 8")
        print("E3342 and E3545: all commutative binary terms excluded by order 8")
        print("E1483: proposed idempotent adjacency is not transitive (order 9)")
        print("E3342 → E3545: the 22-leaf candidate is refuted by order 8")
        print("Certificate tables match. No general definability cell is settled.")


if __name__ == "__main__":
    main()

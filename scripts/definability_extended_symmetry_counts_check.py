#!/usr/bin/env python3
"""Check and reproduce the larger fixed-cycle counting certificates."""

import argparse
import json
from pathlib import Path

from definability_matrix_counts_check import table_counts
from definability_symmetry_counts_check import permutation_tables, render
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/definability_extended_symmetry_counts.json"
GENERATED = ROOT / "equational_theories/Definability/Generated"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(DATA.read_text())
    entries = data["candidates"]
    equations = load_equations()
    for permutation in sorted({tuple(e["permutation"]) for e in entries}):
        batch = [e for e in entries if tuple(e["permutation"]) == permutation]
        tables = permutation_tables(permutation)
        ids = sorted({e[key] for e in batch for key in ("source", "target")})
        counts = table_counts(equations, ids, tables)
        for e in batch:
            assert len(tables) == e["family_count"]
            assert counts[e["source"]] == e["source_count"]
            assert counts[e["target"]] == e["target_count"]
            assert e["source_count"] > e["target_count"]
        print(
            f"Checked {len(tables):,} compatible operations for {len(batch)} candidate pairs."
        )
    assert sorted(i for part in data["parts"] for i in part) == sorted(
        data["selected_indices"]
    )
    assert set().union(*(set(c) for _, c in data["coverage"])) == set(
        range(len(entries))
    )
    for part, indices in enumerate(data["parts"]):
        path = GENERATED / f"ExtendedSymmetryCount{part}.lean"
        text = (
            render([entries[i] for i in indices])
            .replace(
                "definability_symmetry_counts_check.py",
                "definability_extended_symmetry_counts_check.py",
            )
            .replace("_symmetryCount", "_extendedSymmetryCount")
        )
        if args.write:
            path.write_text(text)
        else:
            assert path.read_text() == text, f"regenerate {path} with --write"
    print(
        f"Reproduced {len(data['selected_indices'])} declarations for {len(entries)} candidate cells."
    )


if __name__ == "__main__":
    main()

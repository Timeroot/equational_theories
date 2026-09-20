#!/usr/bin/env python3
"""Check and reproduce the additional large-modulus linear certificates."""

import argparse
from functools import lru_cache
import json
from pathlib import Path

from definability_linear_counts import linear_models
from definability_partial_counts_check import render as render_partial
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/definability_large_linear_counts.json"
OUTPUT = ROOT / "equational_theories/Definability/Generated/LargeLinearCount.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(DATA.read_text())
    equations = load_equations()

    @lru_cache(None)
    def models(law, modulus):
        return linear_models(equations[law - 1], modulus)

    entries = data["candidates"]
    for entry in entries:
        source = models(entry["source"], entry["modulus"])
        target = models(entry["target"], entry["modulus"])
        factors = list(map(tuple, entry["factors"]))
        assert len(source) == entry["source_count"]
        assert len(target) == entry["target_count"]
        assert len(set(factors)) == len(factors) == len(target) + 1
        assert set(factors) <= set(source)
    selected = data["selected_indices"]
    text = (
        render_partial([entries[i] for i in selected])
        .replace(
            "definability_partial_counts_check.py",
            "definability_large_linear_counts_check.py",
        )
        .replace("_partialLinearCount", "_largeLinearCount")
    )
    if args.write:
        OUTPUT.write_text(text)
    else:
        assert OUTPUT.read_text() == text, "regenerate with --write"
    print(
        f"Verified {len(entries)} count certificates; reproduced {len(selected)} declarations."
    )


if __name__ == "__main__":
    main()

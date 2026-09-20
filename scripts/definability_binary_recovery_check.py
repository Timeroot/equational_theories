#!/usr/bin/env python3
"""Check finite companions with identical compatible binary relations.

Two-position local interpolation in both directions is equivalent to equality
of the compatible binary-relation families. This does not establish actual
defining terms: compatible relations of higher arities may still separate them.
"""

import json
from pathlib import Path

import numpy as np

from definability_bolan_recovery_check import local_relations, proper_subalgebras
from definability_twisted_check import satisfies
from spectrum_generate import load_equations


def main():
    path = (
        Path(__file__).resolve().parent.parent
        / "data/definability_binary_recovery_candidates.json"
    )
    entries = json.loads(path.read_text())["candidates"]
    equations = load_equations()
    assert len(entries) == 6
    for entry in entries:
        n = entry["order"]
        source = np.array(entry["source_table"], dtype=np.int32)
        target = np.array(entry["target_table"], dtype=np.int32)
        assert source.shape == target.shape == (n, n)
        assert satisfies(equations[entry["source"] - 1], source)
        assert satisfies(equations[entry["target"] - 1], target)
        counts = []
        for base, derived in ((source, target), (target, source)):
            relations = local_relations(base)
            flat = derived.ravel()
            assert all(n * int(flat[c]) + int(flat[d]) in r for c, d, r in relations)
            counts.append(len(relations))
        assert proper_subalgebras(source) == proper_subalgebras(target)
        print(
            f"E{entry['source']} → E{entry['target']}, order {n}: compatible binary "
            f"relations agree ({counts[0]}/{counts[1]} proper local closures).",
            flush=True,
        )
    print(
        "No defining term, mutual term recovery, or definability-table cell is established."
    )


if __name__ == "__main__":
    main()

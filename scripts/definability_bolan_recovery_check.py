#!/usr/bin/env python3
"""Check finite target tables surviving the Bolan-model recovery constraints.

These tables are not known to be source terms. They show that all one- and
two-position interpolation constraints, even together with equality of the
subalgebra families, do not refute these particular companions.
"""

import itertools
import json
from pathlib import Path

import numpy as np

from definability_twisted_check import satisfies
from spectrum_generate import load_equations


ROOT = Path(__file__).resolve().parent.parent


def source_table(n):
    text = (
        ROOT / "equational_theories/Spectrum/Generated/CentralWitnesses.lean"
    ).read_text()
    literal = (
        text.split(f"def table_1486_{n} :", 1)[1]
        .split(" x y⟩", 1)[0]
        .split("=>", 1)[1]
        .strip()
    )
    table = np.array(json.loads(literal.replace("!", "")), dtype=np.int32)
    assert table.shape == (n, n)
    return table


def local_relations(table):
    """Recompute every proper closure of two seeds in the square algebra."""
    n = len(table)
    a, b = np.divmod(np.arange(n * n), n)
    product = n * table[a[:, None], a[None, :]] + table[b[:, None], b[None, :]]
    cells = list(itertools.product(range(n), repeat=2))
    relations = []
    for c, d in itertools.combinations_with_replacement(range(n * n), 2):
        x, y = cells[c]
        z, w = cells[d]
        members = np.unique([n * x + z, n * y + w])
        while len(members) != n * n:
            enlarged = np.union1d(members, product[np.ix_(members, members)])
            if len(enlarged) == len(members):
                break
            members = enlarged
        if len(members) != n * n:
            relations.append((c, d, set(map(int, members))))
    return relations


def proper_subalgebras(table):
    n = len(table)
    result = set()
    for mask in range(1, (1 << n) - 1):
        members = [x for x in range(n) if mask >> x & 1]
        if all(mask >> int(table[x, y]) & 1 for x in members for y in members):
            result.add(mask)
    return result


def main():
    data = json.loads(
        (ROOT / "data/definability_bolan_recovery_candidates.json").read_text()
    )
    equations = load_equations()
    assert data["source"] == 1486
    for n in (11, 13):
        source = source_table(n)
        assert satisfies(equations[1485], source)
        relations = local_relations(source)
        closed = proper_subalgebras(source)
        assert len(relations) == {11: 2025, 13: 670}[n]
        assert closed == {11: {1, 128, 512, 785}, 13: {1, 128, 4096}}[n]
        for entry in data["candidates"]:
            if entry["order"] != n:
                continue
            target = np.array(entry["table"], dtype=np.int32)
            assert target.shape == (n, n)
            assert satisfies(equations[entry["target"] - 1], target)
            flat = target.ravel()
            assert all(n * int(flat[c]) + int(flat[d]) in r for c, d, r in relations)
            assert proper_subalgebras(target) == closed
            print(
                f"Order {n}, E{entry['target']}: all {len(relations)} proper local "
                f"relations and all {len(closed)} proper subalgebras verified.",
                flush=True,
            )
    print("These finite witnesses establish no definability-table cell.")


if __name__ == "__main__":
    main()

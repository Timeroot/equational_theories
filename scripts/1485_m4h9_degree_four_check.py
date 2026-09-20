#!/usr/bin/env python3
"""Check the isolated-parameter degree-four footprint at r=3,m=4,h=9.

This imports the exhaustive central-incidence generator, not a magma or
SAT solver. The analytic parameter-separation lemma is documented in
docs/1485_four_central_degree_four.md. No Lean result is asserted.
"""

from collections import Counter
from importlib import import_module
from itertools import combinations


incidence = import_module("1485_m4h9_incidence_check")


def shared_parameter_pair(rectangles):
    rows = [{t for t, (p, _) in enumerate(rectangles) if z in p}
            for z in range(4)]
    columns = [{t for t, (_, c) in enumerate(rectangles) if z in c}
               for z in range(4)]
    return any(rows[i] == rows[j] or columns[i] == columns[j]
               for i, j in combinations(range(4), 2))


def main():
    diagrams = list(incidence.diagrams())
    assert len(diagrams) == 285
    histogram = Counter()
    survivors = []
    packing_histogram = Counter()
    for rectangles in diagrams:
        profiles = incidence.profiles(rectangles)
        central = [[bool(set(c) & set(p)) for p, _ in rectangles]
                   for _, c in rectangles]
        good = [frozenset((u, v) for u in p for v in q if not central[u][v])
                for p, q in profiles]
        packing = max((size for size in range(len(profiles) + 1)
                       if any(all(not (good[i] & good[j])
                                  for i, j in combinations(indices, 2))
                              for indices in combinations(range(len(profiles)), size))),
                      default=0)
        packing_histogram[packing] += 1
        shared = shared_parameter_pair(rectangles)
        if profiles:
            histogram[shared, len(profiles)] += 1
        if shared:
            continue
        assert len(profiles) <= 1
        if profiles:
            p, q = profiles[0]
            assert not (set(p) & set(q))
            assert len(good[0]) == 6
            survivors.append(rectangles)
    assert packing_histogram == Counter({0: 231, 1: 52, 2: 2})
    assert histogram == Counter({(False, 1): 24, (True, 2): 24, (True, 4): 6})
    assert len(survivors) == 24
    assert len({incidence.canonical(r) for r in survivors}) == 6
    print("All 285 central-incidence diagrams checked.")
    print("Good-profile packing histogram:", dict(sorted(packing_histogram.items())))
    print("24 no-sharing diagrams have one degree-four profile each;")
    print("every such profile has disjoint top predecessor/successor sets.")
    print("These form six central-relabeling/duality orbits.")


if __name__ == "__main__":
    main()

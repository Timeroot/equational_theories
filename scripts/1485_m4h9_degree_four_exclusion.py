#!/usr/bin/env python3
"""Check the final r=3,m=4,h=9, least-degree-four incidence exclusion.

This checks finite central incidence, not magma tables or SAT instances.
No Lean theorem is asserted.
"""

from collections import Counter
from importlib import import_module
from itertools import combinations, product


incidence = import_module("1485_m4h9_incidence_check")
degree_four = import_module("1485_m4h9_degree_four_check")
CENTRAL = frozenset(range(4))
TOP = range(9)


def partitions(rectangles, side):
    """All top subsets whose indicated central labels partition Z."""
    return [frozenset(subset)
            for size in (2, 3, 4) for subset in combinations(TOP, size)
            if all(sum(z in rectangles[t][side] for t in subset) == 1
                   for z in CENTRAL)]


def analyze(rectangles):
    profiles = incidence.profiles(rectangles)
    assert len(profiles) == 1
    u_a, v_a = profiles[0]
    central_pairs = {(u, v) for u, v in product(TOP, repeat=2)
                     if set(rectangles[u][1]) & set(rectangles[v][0])}
    a_pairs = set(product(u_a, v_a)) - central_pairs
    assert len(a_pairs) == 6
    candidates = []
    for u, v in product(partitions(rectangles, 0), partitions(rectangles, 1)):
        # Exact complementary-degree balance forces equal top counts.
        if len(u) != len(v):
            continue
        size = len(u)
        good = set(product(u, v)) - central_pairs - a_pairs
        if not good:
            continue
        row_counts = [sum((t, w) in good for w in v) for t in u]
        column_counts = [sum((t, w) in good for t in u) for w in v]
        for sharp in (1, 2, 3):
            # The sole possible non-top, non-sharp neighbor is b,
            # the unique vertex of complementary degree four.
            adjacent_b = 5 - size - sharp
            if adjacent_b not in (0, 1):
                continue
            if not all(3 - sharp - adjacent_b <= count <= 3 - sharp
                       for count in row_counts + column_counts):
                continue
            # If b is a neighbor, it fills at least size-1 top fibers.
            if len(good) > size * (3 - sharp) - adjacent_b * (size - 1):
                continue
            candidates.append((u, v, sharp, frozenset(good)))
    low_pairs = central_pairs | a_pairs
    for _, _, _, good in candidates:
        low_pairs.update(good)

    # Refined packing: if t->u and |P_t|=2, every u*w with
    # C_w meeting P_t has degree at most five.
    allowed_edges = {(t, u) for t, u in product(TOP, repeat=2)
                     if len(rectangles[t][0]) == 1
                     or all((u, w) in low_pairs for w in TOP
                            if (w, t) in central_pairs)}
    missing_rows = [(t, z) for t, z in product(TOP, CENTRAL)
                    if not any((t, u) in allowed_edges and z in rectangles[u][1]
                               for u in TOP)]
    missing_columns = [(u, z) for u, z in product(TOP, CENTRAL)
                       if not any((t, u) in allowed_edges and z in rectangles[t][0]
                                  for t in TOP)]
    # Either violates DC=J or BD=J. Union-cover failure is enough;
    # no exact-cover search for the ordinary top adjacency is used.
    assert missing_rows or missing_columns
    return candidates, low_pairs, missing_rows, missing_columns


def main():
    diagrams = list(incidence.diagrams())
    assert len(diagrams) == 285
    surviving = [r for r in diagrams if incidence.profiles(r)
                 and not degree_four.shared_parameter_pair(r)]
    assert len(surviving) == 24
    histogram = Counter()
    for rectangles in surviving:
        candidates, _, _, _ = analyze(rectangles)
        histogram[len(candidates)] += 1
    representatives = sorted({incidence.canonical(r) for r in surviving})
    assert len(representatives) == 6
    print("All 285 diagrams checked: 261 removed by the degree-four reduction;")
    print("all remaining 24 violate a central-label coverage condition.")
    print("Degree-five candidate-count histogram:", dict(sorted(histogram.items())))
    print()
    print("| Rectangle table | Degree-five profiles | Degree-five pair cover | Witness |")
    print("| --- | ---: | ---: | --- |")
    for rectangles in representatives:
        candidates, low_pairs, rows, columns = analyze(rectangles)
        encoded, _ = incidence.display(rectangles, [])
        # There are 36 central and six degree-four pairs.
        assert len(low_pairs) >= 42
        witness = ("row " if rows else "column ") + str((rows or columns)[0])
        print(f"| `{encoded}` | {len(candidates)} | {len(low_pairs) - 42} | {witness} |")


if __name__ == "__main__":
    main()

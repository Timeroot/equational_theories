#!/usr/bin/env python3
"""Finite top-profile proof excluding exactly two degree-four vertices.

Assumptions and the analytic reduction are documented in
docs/1485_three_central_two_degree_four_exclusion.md.
This is not a magma enumeration, SAT search, or Lean theorem.
"""

from collections import Counter
from itertools import combinations, permutations, product


LABELS = range(3)
TOP = tuple(product(LABELS, repeat=2))
CENTRAL_PAIRS = frozenset((u, v) for u, v in product(TOP, repeat=2)
                          if u[1] == v[0])


def predecessor_profile(function):
    return frozenset((i, function[i]) for i in LABELS)


def successor_profile(function):
    return frozenset((function[j], j) for j in LABELS)


def degree_five_candidates(degree_four_pairs, profiles):
    """An overapproximation: no coexistence of the returned profiles is assumed."""
    result = []
    for u_profile, v_profile in profiles:
        good = (set(product(u_profile, v_profile))
                - CENTRAL_PAIRS - degree_four_pairs)
        if not 3 <= len(good) <= 4:
            continue
        rows = {u: sum((u, v) in good for v in v_profile) for u in u_profile}
        columns = {v: sum((u, v) in good for u in u_profile) for v in v_profile}
        if not all(1 <= count <= 2 for count in (*rows.values(), *columns.values())):
            continue
        allowed = True
        for u, v in good:
            third = next(k for k in LABELS if k not in (u[1], v[0]))
            if rows[u] == 2 and (u, (third, v[1])) not in degree_four_pairs:
                allowed = False
                break
            if columns[v] == 2 and ((u[0], third), v) not in degree_four_pairs:
                allowed = False
                break
        if allowed:
            result.append((u_profile, v_profile, frozenset(good)))
    return result


def missed_triples(low_pairs):
    missing = sum(not any((u, (k, column)) in low_pairs
                          for k in LABELS if k != u[1])
                  for u in TOP for column in LABELS)
    return missing + sum(not any(((row, j), v) in low_pairs
                                 for j in LABELS if j != v[0])
                         for v in TOP for row in LABELS)


def main():
    functions = list(product(LABELS, repeat=3))
    permutation_functions = list(permutations(LABELS))
    degree_four = [frozenset(product(predecessor_profile(f), successor_profile(g)))
                   - CENTRAL_PAIRS
                   for f, g in product(permutation_functions, repeat=2)]
    assert len(degree_four) == len(set(degree_four)) == 36
    assert all(len(good) == 6 for good in degree_four)
    unions = {a | b for a, b in combinations(degree_four, 2) if not a & b}
    assert len(unions) == 414
    profiles = [(predecessor_profile(f), successor_profile(g))
                for f, g in product(functions, repeat=2)]
    assert len(profiles) == 729

    histogram = Counter()
    for degree_four_pairs in unions:
        degree_five_cover = set()
        candidates = degree_five_candidates(degree_four_pairs, profiles)
        for _, _, good in candidates:
            degree_five_cover.update(good)
        low_pairs = degree_four_pairs | degree_five_cover
        missing = missed_triples(low_pairs)
        # Every central-column triple and its dual needs a degree-4/5 output.
        assert missing > 0
        histogram[len(candidates), len(degree_five_cover), missing] += 1

    expected = Counter({(4, 10, 19): 216, (0, 0, 33): 72, (6, 10, 20): 54,
                        (0, 0, 30): 36, (18, 24, 12): 36})
    assert histogram == expected
    print("All 414 disjoint pairs of degree-four profiles checked.")
    print("Each leaves at least 12 unserved central-column/row triples.")
    print("(Degree-five candidates, pair cover, missed triples): diagram count")
    for signature, count in sorted(histogram.items()):
        print(signature, ":", count)


if __name__ == "__main__":
    main()

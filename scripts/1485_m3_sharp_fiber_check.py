#!/usr/bin/env python3
"""Finite mixed-sharp-fiber exclusions for 3, 4, or 5 degree-four vertices.

This checks necessary profiles and sharp maps, not magma tables or SAT.
See docs/1485_three_central_four_five_degree_four_exclusion.md.
Simultaneous codomain relabeling is normalized by the first occurrence
order in F; G is still enumerated over all onto maps to the same labels.
"""

import argparse
from collections import Counter
from importlib import import_module
from itertools import combinations, permutations, product


base = import_module("1485_m3_two_degree_four_check")


def canonical_labels(function):
    return all(value <= max(function[:i], default=-1) + 1
               for i, value in enumerate(function))


def check(size):
    permutations_three = list(permutations(base.LABELS))
    profiles_a = [(base.predecessor_profile(f), base.successor_profile(g))
                  for f, g in product(permutations_three, repeat=2)]
    good_a = [frozenset(product(u, v)) - base.CENTRAL_PAIRS for u, v in profiles_a]
    functions_three = list(product(base.LABELS, repeat=3))
    profiles_c = [(base.predecessor_profile(f), base.successor_profile(g))
                  for f, g in product(functions_three, repeat=2)]
    onto = {b: [f for f in product(range(b), repeat=size) if set(f) == set(range(b))]
            for b in range(2, size + 1)}
    total = preliminary_survivors = valid_maps = 0
    histogram = Counter()

    for indices in combinations(range(36), size):
        if any(good_a[i] & good_a[j] for i, j in combinations(indices, 2)):
            continue
        u_a = [profiles_a[i][0] for i in indices]
        v_a = [profiles_a[i][1] for i in indices]
        bad_middle_pairs = [(i, j) for i, j in product(range(size), repeat=2)
                            if len(v_a[i] & u_a[j]) != 1]
        # For |A|=5, joint injectivity gives |B|>=3. The established
        # parity theorem forces all predecessor profiles to one parity
        # and all successor profiles to the opposite parity. Both
        # choices are retained: there is no parity/relabeling quotient.
        if size == 5 and bad_middle_pairs:
            continue
        total += 1
        degree_four_pairs = frozenset().union(*(good_a[i] for i in indices))
        candidates = base.degree_five_candidates(degree_four_pairs, profiles_c)
        cover = degree_four_pairs.union(*(good for _, _, good in candidates))
        if base.missed_triples(cover):
            continue
        preliminary_survivors += 1

        exceptional = [([i for i in range(size) if len(v_a[i] & u) != 1],
                        [i for i in range(size) if len(u_a[i] & v) != 1])
                       for u, v, _ in candidates]
        overlapping_u = [(i, j) for i, j in combinations(range(size), 2) if u_a[i] & u_a[j]]
        overlapping_v = [(i, j) for i, j in combinations(range(size), 2) if v_a[i] & v_a[j]]
        coverage_cache = {}

        for target_size, functions in onto.items():
            successors = [f for f in functions if canonical_labels(f)
                          and all(f[i] != f[j] for i, j in overlapping_u)]
            predecessors = [g for g in functions
                            if all(g[i] != g[j] for i, j in overlapping_v)]
            # Cache candidate masks for the one-F-fiber / one-G-fiber tests.
            left_masks = {f: sum(1 << j for j, (left, _) in enumerate(exceptional)
                                 if len({f[i] for i in left}) <= 1)
                          for f in successors}
            right_masks = {g: sum(1 << j for j, (_, right) in enumerate(exceptional)
                                  if len({g[i] for i in right}) <= 1)
                           for g in predecessors}

            for successor, predecessor in product(successors, predecessors):
                if len(set(zip(successor, predecessor))) != size:
                    continue
                if any(successor[i] != predecessor[j] for i, j in bad_middle_pairs):
                    continue
                valid_maps += 1
                flags = left_masks[successor] & right_masks[predecessor]
                if flags not in coverage_cache:
                    retained = [candidate for j, candidate in enumerate(candidates) if flags & (1 << j)]
                    cover = degree_four_pairs.union(*(good for _, _, good in retained))
                    coverage_cache[flags] = (len(retained), base.missed_triples(cover))
                retained_count, missing = coverage_cache[flags]
                assert missing > 0
                histogram[target_size, retained_count, missing] += 1

    expected_counts = {3: (1956, 24, 216), 4: (4140, 648, 14004), 5: (252, 162, 321948)}
    assert (total, preliminary_survivors, valid_maps) == expected_counts[size]
    expected_histograms = {
        3: Counter({(2, 0, 18): 96, (2, 3, 12): 48, (3, 0, 18): 72}),
        4: Counter({(2, 0, 12): 408, (2, 1, 11): 48, (2, 2, 10): 24, (2, 3, 8): 24,
                    (3, 0, 12): 11052, (3, 1, 11): 144, (3, 2, 10): 72, (3, 3, 8): 72,
                    (4, 0, 12): 2160}),
        5: Counter({(3, 0, 6): 58428, (3, 0, 9): 30672,
                    (4, 0, 6): 125280, (4, 0, 9): 88128,
                    (5, 0, 6): 10800, (5, 0, 9): 8640}),
    }
    assert histogram == expected_histograms[size]
    print(f"|A|={size}: {total} profile collections, {preliminary_survivors} preliminary survivors.")
    print(f"All {valid_maps} normalized sharp-map cases violate low-output triple coverage.")
    print("(Reciprocal class size, retained degree-five candidates, missed triples): count")
    for signature, count in sorted(histogram.items()):
        print(signature, ":", count)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, choices=(3, 4, 5), required=True)
    args = parser.parse_args()
    check(args.size)


if __name__ == "__main__":
    main()

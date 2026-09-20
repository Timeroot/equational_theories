#!/usr/bin/env python3
"""Check the three-degree-four-vertex exclusion using mixed sharp fibers.

See docs/1485_three_central_three_degree_four_exclusion.md for the reduction.
This is a finite profile enumeration, not a SAT or Lean proof.
"""

from collections import Counter
from importlib import import_module
from itertools import combinations, permutations, product


base = import_module("1485_m3_two_degree_four_check")


def sharp_maps(size):
    for target_size in range(2, size + 1):
        functions = [f for f in product(range(target_size), repeat=size)
                     if set(f) == set(range(target_size))]
        for successor, predecessor in product(functions, repeat=2):
            if len(set(zip(successor, predecessor))) == size:
                yield target_size, successor, predecessor


def main():
    permutation_functions = list(permutations(base.LABELS))
    profiles_a = [(base.predecessor_profile(f), base.successor_profile(g))
                  for f, g in product(permutation_functions, repeat=2)]
    good_a = [frozenset(product(u, v)) - base.CENTRAL_PAIRS for u, v in profiles_a]
    functions = list(product(base.LABELS, repeat=3))
    profiles_c = [(base.predecessor_profile(f), base.successor_profile(g))
                  for f, g in product(functions, repeat=2)]
    total = surviving_collections = valid_maps = 0
    histogram = Counter()
    maps = list(sharp_maps(3))
    assert Counter(b for b, _, _ in maps) == Counter({2: 24, 3: 36})

    for indices in combinations(range(36), 3):
        if any(good_a[i] & good_a[j] for i, j in combinations(indices, 2)):
            continue
        total += 1
        degree_four_pairs = frozenset().union(*(good_a[i] for i in indices))
        candidates = base.degree_five_candidates(degree_four_pairs, profiles_c)
        cover = degree_four_pairs.union(*(good for _, _, good in candidates))
        if base.missed_triples(cover):
            continue
        surviving_collections += 1
        u_a = [profiles_a[i][0] for i in indices]
        v_a = [profiles_a[i][1] for i in indices]
        # This structural description is checked, not assumed by the enumeration.
        assert all(not (u_a[i] & u_a[j]) and not (v_a[i] & v_a[j])
                   for i, j in combinations(range(3), 2))
        exceptional = [([i for i in range(3) if len(v_a[i] & u) != 1],
                        [i for i in range(3) if len(u_a[i] & v) != 1])
                       for u, v, _ in candidates]
        for target_size, successor, predecessor in maps:
            # If there is no sharp B-middle of an A×A endpoint pair,
            # its top middle must be unique.
            if any(successor[i] != predecessor[j] and len(v_a[i] & u_a[j]) != 1
                   for i, j in product(range(3), repeat=2)):
                continue
            valid_maps += 1
            retained = [candidate for candidate, (left, right)
                        in zip(candidates, exceptional)
                        if len({successor[i] for i in left}) <= 1
                        and len({predecessor[i] for i in right}) <= 1]
            cover = degree_four_pairs.union(*(good for _, _, good in retained))
            missing = base.missed_triples(cover)
            assert missing > 0
            histogram[target_size, len(retained), missing] += 1

    assert total == 1956
    assert surviving_collections == 24
    assert valid_maps == 720
    assert histogram == Counter({(2, 0, 18): 192, (2, 3, 12): 96, (3, 0, 18): 432})
    print("All 1956 disjoint triples of degree-four profiles checked.")
    print("24 survive initial coverage; all 720 compatible sharp-map cases fail.")
    print("(Reciprocal class size, degree-five candidates, missed triples): count")
    for signature, count in sorted(histogram.items()):
        print(signature, ":", count)


if __name__ == "__main__":
    main()

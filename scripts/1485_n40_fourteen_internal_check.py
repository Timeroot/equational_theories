#!/usr/bin/env python3
"""Necessary six-vertex incidence checks for |A5|=14 at order forty.

See docs/1485_order_forty_near_saturation.md.  This does NOT exclude
|A5|=14: three isomorphism types survive.  It excludes one sharp-degree
distribution and classifies the survivors of the stated necessary tests.
All arithmetic is exact; no SAT, magma-table search, or external package.
"""

from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter


def five_cycles_allowed(internal, sharp_paths):
    """Five-cycle consequences for the two noncentral non-top degrees.

    With one A vertex, just two positions can be bad.  With two A
    vertices every position is good, so that case adds no constraint.
    Repeated vertices in a directed closed walk are allowed.
    """
    for a in range(6):
        for b in internal[a]:
            for c in internal[b]:
                for d in internal[c]:
                    if a in sharp_paths[d] and (
                        (c in sharp_paths[a]) != (d in sharp_paths[b])
                    ):
                        return False
                    for e in internal[d]:
                        if a not in internal[e]:
                            continue
                        cycle = a, b, c, d, e
                        bad_mask = sum(
                            (cycle[(i + 2) % 5] in sharp_paths[cycle[i]]) << i
                            for i in range(5)
                        )
                        if bad_mask not in (0, 31, 3, 6, 12, 24, 17):
                            return False
    return True


def return_matching_allowed(internal, sharp_paths, sharp):
    """A top return has at most 4-j_a-j_d all-B good-good paths."""
    for a, d in product(range(6), repeat=2):
        if a in sharp_paths[d] or any(a in internal[k] for k in internal[d]):
            continue
        good_good = sum(
            c not in sharp_paths[a] and d not in sharp_paths[b]
            for b in internal[a] for c in internal[b] if d in internal[c]
        )
        if good_good > 4 - sharp[a] - sharp[d]:
            return False
    return True


def enumerate_incidence(sharp):
    """Enumerate D, then the possible binary sharp-path matrices C."""
    degrees = [4 - j for j in sharp]
    options = [tuple(combinations(range(6), degree)) for degree in degrees]
    capacities = degrees[:]
    internal = []
    counts = Counter()
    survivors = []

    def inspect_graph():
        counts["internal_graphs"] += 1
        square = [
            [sum(j in internal[k] for k in internal[i]) for j in range(6)]
            for i in range(6)
        ]
        forced = [
            {
                j for j in range(6)
                if square[i][j] >= 2
                or (square[i][j] == 0 and sharp[i] + sharp[j] > 4)
            }
            for i in range(6)
        ]
        if any(len(forced[i]) > sharp[i] for i in range(6)):
            counts["forced_row_exclusions"] += 1
            return
        remaining_columns = [sharp[j] - sum(j in row for row in forced) for j in range(6)]
        if min(remaining_columns) < 0:
            counts["forced_column_exclusions"] += 1
            return
        additions = [
            tuple(combinations([j for j in range(6) if j not in forced[i]],
                               sharp[i] - len(forced[i])))
            for i in range(6)
        ]
        order = sorted(range(6), key=lambda i: len(additions[i]))
        sharp_paths = [set(row) for row in forced]

        def complete(depth):
            if depth == 6:
                assert not any(remaining_columns)
                counts["sharp_path_completions"] += 1
                if five_cycles_allowed(internal, sharp_paths):
                    counts["five_cycle_survivors"] += 1
                    survivors.append((tuple(internal),
                                      tuple(tuple(sorted(row)) for row in sharp_paths)))
                return
            i = order[depth]
            for choice in additions[i]:
                if any(remaining_columns[j] == 0 for j in choice):
                    continue
                for j in choice:
                    remaining_columns[j] -= 1
                sharp_paths[i].update(choice)
                complete(depth + 1)
                sharp_paths[i].difference_update(choice)
                for j in choice:
                    remaining_columns[j] += 1

        complete(0)

    def extend(depth):
        if depth == 6:
            assert not any(capacities)
            inspect_graph()
            return
        for row in options[depth]:
            if any(capacities[j] == 0 for j in row):
                continue
            for j in row:
                capacities[j] -= 1
            if max(capacities) <= 5 - depth:
                internal.append(row)
                extend(depth + 1)
                internal.pop()
            for j in row:
                capacities[j] += 1

    extend(0)
    return counts, survivors


def canonical_pair(pair, sharp):
    classes = [[i for i, value in enumerate(sharp) if value == j] for j in sorted(set(sharp))]
    representatives = []
    for parts in product(*(permutations(group) for group in classes)):
        mapping = {i: j for group, part in zip(classes, parts) for i, j in zip(group, part)}
        transformed = []
        for matrix in pair:
            image = [None] * 6
            for i, row in enumerate(matrix):
                image[mapping[i]] = tuple(sorted(mapping[j] for j in row))
            transformed.append(tuple(image))
        representatives.append(tuple(transformed))
    return min(representatives)


def main():
    started = perf_counter()
    first_counts, first_survivors = enumerate_incidence((1, 2, 2, 3, 3, 3))
    assert first_counts["internal_graphs"] == 3358
    assert first_counts["sharp_path_completions"] == 24
    assert not first_survivors
    print("Sharp counts (1,2,2,3,3,3): EXCLUDED by necessary five-cycle tests")
    print(dict(first_counts))

    sharp = (1, 1, 3, 3, 3, 3)
    second_counts, survivors = enumerate_incidence(sharp)
    assert second_counts["internal_graphs"] == 1032
    assert second_counts["sharp_path_completions"] == 336
    assert len(survivors) == 48
    classes = Counter(canonical_pair(pair, sharp) for pair in survivors)
    assert sorted(classes.values()) == [6, 6, 12, 24]
    for internal, sharp_paths in classes:
        assert sharp_paths[0] == (0,) and sharp_paths[1] == (1,)
        missing = [set(range(2, 6)) - set(sharp_paths[i]) for i in range(2, 6)]
        assert all(len(row) == 1 for row in missing)
        assert len(set.union(*missing)) == 4
        assert all(set(internal[i]) <= {0, 1} for i in range(2, 6))
    print("Sharp counts (1,1,3,3,3,3): four types after five-cycle tests")
    print(dict(second_counts))
    for index, ((internal, sharp_paths), multiplicity) in enumerate(sorted(classes.items()), 1):
        missing = tuple(next(iter(set(range(2, 6)) - set(sharp_paths[i]))) for i in range(2, 6))
        print(f"Type {index}: multiplicity={multiplicity}; D rows={internal}; high C omissions={missing}")
    final = [pair for pair in survivors if return_matching_allowed(*pair, sharp)]
    final_classes = Counter(canonical_pair(pair, sharp) for pair in final)
    assert len(final) == 24 and sorted(final_classes.values()) == [6, 6, 12]
    print("After good-return matching: 24 labeled pairs, THREE types survive; |A5|=14 NOT EXCLUDED")
    print(f"Elapsed: {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()

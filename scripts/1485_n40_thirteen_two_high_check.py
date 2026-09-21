#!/usr/bin/env python3
"""Exact necessary-incidence exclusions with one or two high-sharp A13 partners.

The default checks sharp pattern 1,1,1,2,2,3,3; --one-high checks
1,1,2,2,2,2,3. This checks two seven-point
binary incidence matrices, not a forty-point magma table. It uses only the
Python standard library; there is no SAT call or imported certificate.
The other A13 sharp distributions are outside this check's scope.
"""

import argparse
from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter


N = 7
SHARP = (1, 1, 1, 2, 2, 3, 3)
DEGREE = tuple(4 - j for j in SHARP)


def mask(indices):
    return sum(1 << i for i in indices)


def canonical_pair(rows, sharp_paths):
    """For reporting only: relabel within the three sharp-degree classes."""
    classes = tuple(tuple(i for i, j in enumerate(SHARP) if j == value)
                    for value in sorted(set(SHARP)))
    images = []
    for pieces in product(*(permutations(part) for part in classes)):
        mapping = dict(zip(range(N), sum(pieces, ())))
        pair = []
        for table in (rows, sharp_paths):
            transformed = [None] * N
            for i, row in enumerate(table):
                transformed[mapping[i]] = tuple(sorted(mapping[j] for j in row))
            pair.append(tuple(transformed))
        images.append(tuple(pair))
    return min(images)


def return_obstruction(rows, sharp_masks, square):
    """Exhibit too many good-good B paths d→x→y→b for the return b*d."""
    for d, b in product(range(N), repeat=2):
        fiber = (8 if sharp_masks[b] >> d & 1 else
                 5 if square[b][d] else 4)
        budget = fiber - SHARP[b] - SHARP[d]
        good_paths = tuple(
            (d, x, y, b)
            for x in rows[d] for y in rows[x]
            if b in rows[y]
            and not (sharp_masks[d] >> y & 1)
            and not (sharp_masks[x] >> b & 1)
        )
        if len(good_paths) > budget:
            return b, d, fiber, budget, good_paths
    return None


def check():
    options = tuple(tuple(combinations(range(N), d)) for d in DEGREE)
    capacities = list(DEGREE)
    rows = []
    counts = Counter()
    types_before_matching = Counter()

    def inspect_graph():
        counts["internal_graphs"] += 1
        row_masks = tuple(mask(row) for row in rows)
        column_masks = tuple(mask(i for i in range(N) if j in rows[i])
                             for j in range(N))
        square = tuple(tuple((row_masks[i] & column_masks[j]).bit_count()
                             for j in range(N)) for i in range(N))
        forced = [mask(j for j in range(N)
                       if square[i][j] >= 2
                       or SHARP[i] + SHARP[j] > 5
                       or (square[i][j] == 0 and SHARP[i] + SHARP[j] > 4))
                  for i in range(N)]
        if any(forced[i].bit_count() > SHARP[i] for i in range(N)):
            return
        remaining = [SHARP[j] - sum(row >> j & 1 for row in forced)
                     for j in range(N)]
        if min(remaining) < 0:
            return
        counts["graphs_after_forced_counts"] += 1
        additions = [tuple(combinations(
            [j for j in range(N) if not (forced[i] >> j & 1)],
            SHARP[i] - forced[i].bit_count())) for i in range(N)]
        order = sorted(range(N), key=lambda i: len(additions[i]))
        sharp_masks = forced[:]

        def inspect_completion():
            counts["sharp_path_completions"] += 1
            sharp_columns = tuple(mask(i for i in range(N)
                                       if sharp_masks[i] >> j & 1)
                                  for j in range(N))
            for b in range(N):
                for d in rows[b]:
                    beta = (sharp_masks[b] & row_masks[d]).bit_count()
                    eta = (column_masks[b] & sharp_columns[d]).bit_count()
                    if beta != eta:
                        return
            counts["after_edge_balance"] += 1
            for a in range(N):
                for b in rows[a]:
                    for c in rows[b]:
                        for d in rows[c]:
                            if (sharp_masks[d] >> a & 1) and (
                                (sharp_masks[a] >> c & 1) !=
                                (sharp_masks[b] >> d & 1)
                            ):
                                return
            counts["after_one_A_closure"] += 1
            sharp_rows = tuple(tuple(j for j in range(N)
                                     if sharp_masks[i] >> j & 1)
                               for i in range(N))
            types_before_matching[canonical_pair(tuple(rows), sharp_rows)] += 1
            if return_obstruction(rows, sharp_masks, square) is None:
                counts["after_return_matching"] += 1

        def complete(depth):
            if depth == N:
                assert not any(remaining)
                inspect_completion()
                return
            i = order[depth]
            for choice in additions[i]:
                if any(remaining[j] == 0 for j in choice):
                    continue
                for j in choice:
                    remaining[j] -= 1
                sharp_masks[i] = forced[i] | mask(choice)
                complete(depth + 1)
                sharp_masks[i] = forced[i]
                for j in choice:
                    remaining[j] += 1

        complete(0)

    def extend(depth):
        if depth == N:
            assert not any(capacities)
            inspect_graph()
            return
        for row in options[depth]:
            if any(capacities[j] == 0 for j in row):
                continue
            for j in row:
                capacities[j] -= 1
            if max(capacities) <= N - 1 - depth:
                rows.append(row)
                extend(depth + 1)
                rows.pop()
            for j in row:
                capacities[j] += 1

    extend(0)
    return counts, types_before_matching


def main():
    global SHARP, DEGREE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--one-high", action="store_true",
                        help="check (1,1,2,2,2,2,3), instead of the default two-high pattern")
    args = parser.parse_args()
    if args.one_high:
        SHARP = (1, 1, 2, 2, 2, 2, 3)
        DEGREE = tuple(4 - j for j in SHARP)
    started = perf_counter()
    counts, classes = check()
    expected = ({
        "internal_graphs": 1413400,
        "graphs_after_forced_counts": 27984,
        "sharp_path_completions": 1547520,
        "after_edge_balance": 3024,
        "after_one_A_closure": 312,
    } if args.one_high else {
        "internal_graphs": 488266,
        "graphs_after_forced_counts": 984,
        "sharp_path_completions": 1512,
        "after_edge_balance": 336,
        "after_one_A_closure": 48,
    })
    assert counts == Counter(expected)
    assert counts["after_return_matching"] == 0
    print(f"EXCLUDED: order 40, A13/B7, sharp counts {SHARP}")
    print(dict(counts))
    print(f"Types before return matching: {len(classes)}")
    for index, ((rows, sharp_rows), multiplicity) in enumerate(sorted(classes.items()), 1):
        sharp_masks = tuple(mask(row) for row in sharp_rows)
        square = tuple(tuple(sum(j in rows[k] for k in rows[i])
                             for j in range(N)) for i in range(N))
        obstruction = return_obstruction(rows, sharp_masks, square)
        assert obstruction is not None
        print(f"Type {index}, {multiplicity} labeled pairs: D={rows}; C={sharp_rows}")
        print(f"  Return obstruction (b,d,fiber,budget,paths): {obstruction}")
    print(f"Elapsed: {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()

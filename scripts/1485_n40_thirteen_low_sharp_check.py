#!/usr/bin/env python3
"""Reduced necessary incidence search for the last A13 sharp distribution.

The analytic premises are:
C has an isolated loop at0, D(0)=Pred_D(0)={1,2,3}, and every internal
edge has exactly one bad extension and predecessor. No SAT or magma-table
search is used. Surviving incidence diagrams, if any, are NOT models.
"""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from time import perf_counter

N = 7
SHARP = (1, 2, 2, 2, 2, 2, 2)
S = (1, 2, 3)
R = (4, 5, 6)


def mask(row):
    return sum(1 << i for i in row)


def canonical(rows, sharp_rows):
    images = []
    for ps, pr in product(permutations(S), permutations(R)):
        mapping = dict(zip(range(N), (0,) + ps + pr))
        pair = []
        for table in (rows, sharp_rows):
            image = [None] * N
            for i, row in enumerate(table):
                image[mapping[i]] = tuple(sorted(mapping[j] for j in row))
            pair.append(tuple(image))
        images.append(tuple(pair))
    return min(images)


def return_failure(rows, sharp, square):
    for d, b in product(range(N), repeat=2):
        fiber = 8 if sharp[b] >> d & 1 else 5 if square[b][d] else 4
        budget = fiber - SHARP[b] - SHARP[d]
        paths = tuple((d, x, y, b) for x in rows[d] for y in rows[x]
                      if b in rows[y] and not (sharp[d] >> y & 1)
                      and not (sharp[x] >> b & 1))
        if len(paths) > budget:
            return b, d, budget, paths
    return None


def inspect_closure(rows, sharp):
    for a in range(N):
        for b in rows[a]:
            for c in rows[b]:
                for d in rows[c]:
                    if sharp[d] >> a & 1 and (
                        (sharp[a] >> c & 1) != (sharp[b] >> d & 1)
                    ):
                        return False
    return True


def inspect_five_walks(rows, sharp):
    # Only the universal rule is used: a bad position cannot have two
    # good adjacent positions. Stronger special-case masks are unnecessary.
    for a in range(N):
        for b in rows[a]:
            for c in rows[b]:
                for d in rows[c]:
                    for e in rows[d]:
                        if a not in rows[e]:
                            continue
                        cycle = a, b, c, d, e
                        bad = tuple(sharp[cycle[i]] >> cycle[(i + 2) % 5] & 1
                                    for i in range(5))
                        if any(bad[i] and not bad[(i - 1) % 5]
                               and not bad[(i + 1) % 5] for i in range(5)):
                            return False
    return True


def check():
    degrees = {i: 1 if i in S else 2 for i in range(1, N)}
    capacities = degrees.copy()
    rows = [S]
    options = {i: tuple(combinations(range(1, N), degrees[i]))
               for i in range(1, N)}
    counts = Counter()
    classes = Counter()

    def inspect_graph():
        counts["normalized_internal_graphs"] += 1
        rm = tuple(mask(row) for row in rows)
        columns = tuple(mask(i for i in range(N) if j in rows[i])
                        for j in range(N))
        square = tuple(tuple((rm[i] & columns[j]).bit_count()
                             for j in range(N)) for i in range(N))
        if any(square[0][j] > 1 or square[j][0] > 1 for j in range(1, N)):
            return
        choices = {}
        for b in range(1, N):
            forced = mask(j for j in range(1, N) if square[b][j] >= 2)
            choices[b] = tuple(mask(pair) for pair in combinations(range(1, N), 2)
                               if mask(pair) & forced == forced
                               and all((mask(pair) & rm[d]).bit_count() == 1
                                       for d in rows[b]))
            if not choices[b]:
                return
        counts["graphs_with_row_choices"] += 1
        order = sorted(range(1, N), key=lambda b: len(choices[b]))
        remaining = [0] + [2] * 6
        sharp = [1] + [0] * 6

        def complete(depth):
            if depth == 6:
                counts["row_balanced_completions"] += 1
                ccol = tuple(mask(i for i in range(N) if sharp[i] >> j & 1)
                             for j in range(N))
                if any((columns[b] & ccol[d]).bit_count() != 1
                       for b in range(N) for d in rows[b]):
                    return
                counts["edge_balanced_completions"] += 1
                if not inspect_closure(rows, sharp):
                    return
                counts["after_one_A_closure"] += 1
                if return_failure(rows, sharp, square) is not None:
                    return
                counts["after_return_matching"] += 1
                if not inspect_five_walks(rows, sharp):
                    return
                counts["after_five_walks"] += 1
                sharp_rows = tuple(tuple(j for j in range(N) if sharp[i] >> j & 1)
                                   for i in range(N))
                classes[canonical(tuple(rows), sharp_rows)] += 1
                return
            b = order[depth]
            for choice in choices[b]:
                targets = tuple(j for j in range(1, N) if choice >> j & 1)
                if any(remaining[j] == 0 for j in targets):
                    continue
                for j in targets:
                    remaining[j] -= 1
                sharp[b] = choice
                complete(depth + 1)
                sharp[b] = 0
                for j in targets:
                    remaining[j] += 1

        complete(0)

    def extend(b):
        if b == N:
            assert not any(capacities.values())
            inspect_graph()
            return
        for choice in options[b]:
            if any(capacities[j] == 0 for j in choice):
                continue
            for j in choice:
                capacities[j] -= 1
            if max(capacities.values()) <= N - 1 - b:
                rows.append(((0,) if b in S else ()) + choice)
                extend(b + 1)
                rows.pop()
            for j in choice:
                capacities[j] += 1

    extend(1)
    return counts, classes


def check_profile_supports():
    """Independently check the final hand proof's coarse support obstructions.

    This uses the 2+1 direction split and low-rank reductions. Relabel P directions by
    K^{-1}, so both attached support rectangles are {0,i} x {0,i},
    with i=1 repeated and i=2 single. No affine offsets, A-vertex labels,
    operation values, or SAT answers enter this check.
    """
    labels = range(4)
    full = tuple(labels)
    profiles = (full,) + tuple(combinations(labels, 2))
    incidence = tuple(tuple((1 if len(support) == 4 else 2)
                            if i in support else 0 for i in labels)
                      for support in profiles)
    by_marginal = {}
    for indices in combinations_with_replacement(range(7), 3):
        margin = tuple(sum(incidence[k][i] for k in indices) for i in labels)
        by_marginal.setdefault(margin, []).append(tuple(profiles[k] for k in indices))

    def active(holes, left, right):
        return sum(p in left and q in right for p, q in holes)

    def margin(holes, coordinate, low_support):
        # The low profile, two repeated attached profiles, and one single
        # attached profile are removed from the full incidence 4+4*holes.
        return tuple(4 + 4 * sum(hole[coordinate] == i for hole in holes)
                     - (1 if len(low_support) == 4 else 2) * (i in low_support)
                     - 4 * (i in (0, 1)) - 2 * (i in (0, 2))
                     for i in labels)

    def compatible(holes, left, right):
        if len(left) == len(right) == 4:
            return False  # At most one good pair per hole, hence at most 3.
        h = active(holes, left, right)
        if len(left) == len(right) == 2:
            # Four good pairs require equal central-label directions;
            # each active hole then contributes either two or four.
            return (left[0] ^ left[1]) == (right[0] ^ right[1]) and h in (1, 2)
        return h >= 2  # At most two good pairs per hole.

    low_cases = tuple((p, q, True) for p in ((0, 1), (2, 3))
                      for q in ((0, 2), (1, 3)))
    low_cases += tuple((full, (0, v), False) for v in (1, 2, 3))
    cells = tuple((p, q) for p, q in product(labels, repeat=2) if (p, q) != (0, 0))
    counts = Counter()
    for holes in combinations(cells, 3):
        if not any(p == 0 for p, q in holes) or not any(q == 0 for p, q in holes):
            continue
        if any(active(holes, (0, i), (0, i)) not in (1, 2) for i in (1, 2)):
            continue
        for low_u, low_v, both_rank_one in low_cases:
            inside = tuple((p, q) for p, q in holes if p in low_u and q in low_v)
            if both_rank_one:
                if len(inside) != 2 or inside[0][0] == inside[1][0] or inside[0][1] == inside[1][1]:
                    continue
            elif len(inside) != 3 or len({p for p, q in holes}) != 3:
                continue
            counts['low_support_cases'] += 1
            u_options = by_marginal.get(margin(holes, 0, low_u), ())
            v_options = by_marginal.get(margin(holes, 1, low_v), ())
            for us, vs in product(u_options, v_options):
                counts['residual_support_pairs'] += 1
                for ordered_vs in set(permutations(vs)):
                    counts['pairings_checked'] += 1
                    if all(compatible(holes, u, v) for u, v in zip(us, ordered_vs)):
                        raise AssertionError(('Unexcluded support case', holes, low_u, low_v, us, ordered_vs))
    return counts


def main():
    started = perf_counter()
    counts, classes = check()
    assert counts == Counter({
        "normalized_internal_graphs": 4383,
        "graphs_with_row_choices": 2628,
        "row_balanced_completions": 23040,
        "edge_balanced_completions": 4752,
        "after_one_A_closure": 84,
        "after_return_matching": 12,
        "after_five_walks": 12,
    })
    assert len(classes) == 1 and tuple(classes.values()) == (12,)
    print(dict(counts))
    print(f"Surviving necessary incidence types: {len(classes)} (not magma models)")
    for i, ((rows, sharp), multiplicity) in enumerate(sorted(classes.items()), 1):
        print(f"Type {i}, {multiplicity} normalized labelings: D={rows}; C={sharp}")
    support_counts = check_profile_supports()
    assert support_counts == Counter(low_support_cases=25,
                                     residual_support_pairs=18, pairings_checked=96)
    print('Final support obstruction:', dict(support_counts), '; no surviving pairing')
    print(f"Elapsed: {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()

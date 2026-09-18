#!/usr/bin/env python3
"""Bounded central-incidence and top-adjacency scan for r=3, m=5, h=9.

Enumerate the two normalized no-full-entry central partition alignments,
then ask for a zero-one, 3-regular top matrix D satisfying BD=DC=J
and the epsilon-one witness condition in both directions. This searches
incidence diagrams, NOT multiplication tables. A survivor is not an E1485
model, and these computations make no claim to settle the spectrum or
the remaining five-central case. The orbit count concerns B,C, not all D.

The script uses only the Python standard library. Every generated B,C
diagram and every returned D is checked directly, independently of the
bit-mask domain filters. Run without Python's -O flag to retain assertions.
"""

from collections import Counter
from itertools import combinations, permutations, product
import json


CENTRAL_POINTS = tuple(range(5))
TOP_VERTICES = tuple(range(9))
PAIRS = tuple(frozenset(pair) for pair in combinations(CENTRAL_POINTS, 2))
FULL_CENTRAL_SQUARE = (1 << 25) - 1
TOP_TRIPLES = tuple(
    sum(1 << vertex for vertex in triple)
    for triple in combinations(TOP_VERTICES, 3)
)
EXPECTED_PROFILE = Counter({(1, 1): 1, (1, 2): 2, (2, 1): 2, (2, 2): 4})


def rectangle_mask(predecessors, successors):
    """Cells of one top vertex's central predecessor/successor rectangle."""
    return sum(1 << (5 * i + j) for i in predecessors for j in successors)


def incidence_matrices(predecessors, successors):
    b = [[int(z in p) for p in predecessors] for z in CENTRAL_POINTS]
    c = [[int(z in q) for z in CENTRAL_POINTS] for q in successors]
    return b, c


def validate_incidence(predecessors, successors):
    """Direct matrix checks, without relying on rectangle-cover bookkeeping."""
    assert len(predecessors) == len(successors) == 9
    assert all(set(p) <= set(CENTRAL_POINTS) for p in predecessors)
    assert all(set(c) <= set(CENTRAL_POINTS) for c in successors)
    assert Counter(zip(map(len, predecessors), map(len, successors))) == EXPECTED_PROFILE

    b, c = incidence_matrices(predecessors, successors)
    assert all(sum(row) == 3 for row in b)
    assert all(sum(c[t][z] for t in TOP_VERTICES) == 3 for z in CENTRAL_POINTS)
    assert all(
        sum(b[z][t] * c[t][w] for t in TOP_VERTICES) == 1
        for z in CENTRAL_POINTS
        for w in CENTRAL_POINTS
    )
    assert all(
        sum(c[t][z] * b[z][u] for z in CENTRAL_POINTS) in (0, 1)
        for t in TOP_VERTICES
        for u in TOP_VERTICES
    )


def diagrams():
    """Generate normalized B,C diagrams, not central-isomorphism orbits.

    The unique (1,1) top has predecessor p=0 and successor q. The
    predecessor pairs of the two (2,1) tops partition Z minus {p}; the
    successor pairs of the two (1,2) tops partition Z minus {q}. Their
    intersections have size at most one. Up to central relabeling and
    reordering those pairs, the two alignments below are p=q and p!=q.

    Four remaining (2,2) rectangles cover the unfilled sixteen cells.
    Choosing a deterministic uncovered cell avoids reordering those four
    rectangles within this parametrization; it does not quotient every
    central relabeling.
    """
    alignments = (
        (0, (frozenset({1, 2}), frozenset({3, 4})),
         (frozenset({1, 3}), frozenset({2, 4}))),
        (1, (frozenset({1, 2}), frozenset({3, 4})),
         (frozenset({0, 3}), frozenset({2, 4}))),
    )
    for alignment, (q, vertical_pairs, horizontal_pairs) in enumerate(alignments):
        for h1, h2, v1, v2 in product(CENTRAL_POINTS, repeat=4):
            initial_predecessors = [
                frozenset({0}), frozenset({h1}), frozenset({h2}),
                *vertical_pairs,
            ]
            initial_successors = [
                frozenset({q}), *horizontal_pairs,
                frozenset({v1}), frozenset({v2}),
            ]
            covered = 0
            for p, c in zip(initial_predecessors, initial_successors):
                cells = rectangle_mask(p, c)
                if covered & cells:
                    break
                covered |= cells
            else:
                if any(
                    len(c & p) > 1
                    for c in initial_successors
                    for p in initial_predecessors
                ):
                    continue
                candidates = [
                    (p, c, rectangle_mask(p, c))
                    for p in PAIRS
                    for c in PAIRS
                    if p not in horizontal_pairs
                    and c not in vertical_pairs
                    and p != c
                    and not rectangle_mask(p, c) & covered
                ]

                def visit(used, chosen):
                    if len(chosen) == 4:
                        if used == FULL_CENTRAL_SQUARE:
                            predecessors = initial_predecessors + [x[0] for x in chosen]
                            successors = initial_successors + [x[1] for x in chosen]
                            validate_incidence(predecessors, successors)
                            yield alignment, predecessors, successors
                        return

                    available = [
                        rectangle for rectangle in candidates
                        if not used & rectangle[2]
                        and all(
                            rectangle[0] != old[1] and rectangle[1] != old[0]
                            for old in chosen
                        )
                    ]
                    choices = None
                    for cell in range(25):
                        if used >> cell & 1:
                            continue
                        here = [x for x in available if x[2] >> cell & 1]
                        if not here:
                            return
                        if choices is None or len(here) < len(choices):
                            choices = here
                    assert choices is not None
                    for rectangle in choices:
                        yield from visit(used | rectangle[2], chosen + [rectangle])

                yield from visit(covered, [])


def partition_domains(sets):
    """Three top vertices whose indicated central sets partition all five points."""
    return [
        mask for mask in TOP_TRIPLES
        if all(
            sum(z in sets[i] for i in TOP_VERTICES if mask >> i & 1) == 1
            for z in CENTRAL_POINTS
        )
    ]


def epsilon_one_ok(mask, missing, witness_masks, weights):
    mids = [i for i in missing if weights[i] == 2]
    lows = [i for i in missing if weights[i] == 1]
    assert len(mids) == 2 and len(lows) == 1
    first, second = [mask & witness_masks[i] for i in mids]
    return first == second and not (first & witness_masks[lows[0]])


def solve_domains(rows, columns):
    """Exhaustive finite row/column-domain search, returning at most one D."""
    while True:
        if any(not domain for domain in rows + columns):
            return None
        old_size = sum(map(len, rows + columns))
        for i in TOP_VERTICES:
            rows[i] = [
                row for row in rows[i]
                if all(
                    any(((column >> i) & 1) == ((row >> j) & 1)
                        for column in columns[j])
                    for j in TOP_VERTICES
                )
            ]
        for j in TOP_VERTICES:
            columns[j] = [
                column for column in columns[j]
                if all(
                    any(((column >> i) & 1) == ((row >> j) & 1)
                        for row in rows[i])
                    for i in TOP_VERTICES
                )
            ]
        if sum(map(len, rows + columns)) == old_size:
            break

    if any(not domain for domain in rows + columns):
        return None
    options = [
        (len(domain), side, i)
        for side, domains in enumerate((rows, columns))
        for i, domain in enumerate(domains)
        if len(domain) > 1
    ]
    if not options:
        return [domain[0] for domain in rows]

    _, side, index = min(options)
    for mask in (rows, columns)[side][index]:
        next_rows = [domain[:] for domain in rows]
        next_columns = [domain[:] for domain in columns]
        (next_rows, next_columns)[side][index] = [mask]
        answer = solve_domains(next_rows, next_columns)
        if answer is not None:
            return answer
    return None


def validate_top_matrix(predecessors, successors, row_masks):
    """Direct checks independent of the search's bit-mask witness filters."""
    assert len(row_masks) == 9
    assert all(0 <= mask < 1 << 9 for mask in row_masks)
    d = [[(mask >> j) & 1 for j in TOP_VERTICES] for mask in row_masks]
    b, c = incidence_matrices(predecessors, successors)
    assert all(sum(row) == 3 for row in d)
    assert all(sum(d[i][j] for i in TOP_VERTICES) == 3 for j in TOP_VERTICES)
    assert all(
        sum(b[z][i] * d[i][j] for i in TOP_VERTICES) == 1
        for z in CENTRAL_POINTS
        for j in TOP_VERTICES
    )
    assert all(
        sum(d[i][j] * c[j][z] for j in TOP_VERTICES) == 1
        for i in TOP_VERTICES
        for z in CENTRAL_POINTS
    )

    for target in TOP_VERTICES:
        if len(predecessors[target]) != 2:
            continue
        missing = [
            source for source in TOP_VERTICES
            if not successors[source] & predecessors[target]
        ]
        mids = [source for source in missing if len(predecessors[source]) == 2]
        lows = [source for source in missing if len(predecessors[source]) == 1]
        assert len(mids) == 2 and len(lows) == 1
        witnesses = {
            source: {
                middle for middle in TOP_VERTICES
                if d[target][middle] and successors[middle] & predecessors[source]
            }
            for source in missing
        }
        assert all(len(witnesses[source]) == len(predecessors[source])
                   for source in missing)
        assert witnesses[mids[0]] == witnesses[mids[1]]
        assert witnesses[mids[0]].isdisjoint(witnesses[lows[0]])

    for source in TOP_VERTICES:
        if len(successors[source]) != 2:
            continue
        missing = [
            target for target in TOP_VERTICES
            if not successors[source] & predecessors[target]
        ]
        mids = [target for target in missing if len(successors[target]) == 2]
        lows = [target for target in missing if len(successors[target]) == 1]
        assert len(mids) == 2 and len(lows) == 1
        witnesses = {
            target: {
                middle for middle in TOP_VERTICES
                if d[middle][source] and successors[target] & predecessors[middle]
            }
            for target in missing
        }
        assert all(len(witnesses[target]) == len(successors[target])
                   for target in missing)
        assert witnesses[mids[0]] == witnesses[mids[1]]
        assert witnesses[mids[0]].isdisjoint(witnesses[lows[0]])


def top_matrix(predecessors, successors):
    """Find one D satisfying the stated necessary conditions, if one exists."""
    k = [[len(c & p) for p in predecessors] for c in successors]
    predecessor_weights = list(map(len, predecessors))
    successor_weights = list(map(len, successors))
    k_columns = [sum(k[b][u] << b for b in TOP_VERTICES) for u in TOP_VERTICES]
    k_rows = [sum(k[u][b] << b for b in TOP_VERTICES) for u in TOP_VERTICES]
    row_base = partition_domains(successors)
    column_base = partition_domains(predecessors)
    rows = []
    columns = []
    for target in TOP_VERTICES:
        missing = [source for source in TOP_VERTICES if not k[source][target]]
        rows.append([
            mask for mask in row_base
            if predecessor_weights[target] != 2
            or epsilon_one_ok(mask, missing, k_columns, predecessor_weights)
        ])
    for source in TOP_VERTICES:
        missing = [target for target in TOP_VERTICES if not k[source][target]]
        columns.append([
            mask for mask in column_base
            if successor_weights[source] != 2
            or epsilon_one_ok(mask, missing, k_rows, successor_weights)
        ])
    answer = solve_domains(rows, columns)
    if answer is not None:
        validate_top_matrix(predecessors, successors, answer)
    return answer


def sharing_signature(predecessors, successors):
    """Component sizes when equal central B-rows or C-columns join points."""
    b_rows = [
        frozenset(i for i, p in enumerate(predecessors) if z in p)
        for z in CENTRAL_POINTS
    ]
    c_columns = [
        frozenset(i for i, c in enumerate(successors) if z in c)
        for z in CENTRAL_POINTS
    ]
    pending = set(CENTRAL_POINTS)
    component_sizes = []
    while pending:
        component = {pending.pop()}
        while True:
            new = {
                j for j in pending
                if any(b_rows[i] == b_rows[j] or c_columns[i] == c_columns[j]
                       for i in component)
            }
            if not new:
                break
            component |= new
            pending -= new
        component_sizes.append(len(component))
    return tuple(sorted(component_sizes))


def canonical_incidence(predecessors, successors):
    """Canonical B,C key; D is deliberately NOT part of this equivalence."""
    candidates = []
    for permutation in permutations(CENTRAL_POINTS):
        p = [sum(1 << permutation[z] for z in points) for points in predecessors]
        c = [sum(1 << permutation[z] for z in points) for points in successors]
        candidates.append(tuple(sorted(zip(p, c))))
        candidates.append(tuple(sorted(zip(c, p))))
    return min(candidates)


def main():
    incidence_counts = Counter()
    survivor_signatures = Counter()
    survivors = []
    for alignment, predecessors, successors in diagrams():
        incidence_counts[alignment] += 1
        d = top_matrix(predecessors, successors)
        if d is None:
            continue
        signature = alignment, sharing_signature(predecessors, successors)
        survivor_signatures[signature] += 1
        survivors.append({
            "P": list(map(sorted, predecessors)),
            "C": list(map(sorted, successors)),
            "D": [[j for j in TOP_VERTICES if mask >> j & 1] for mask in d],
        })

    orbits = {}
    for i, diagram in enumerate(survivors):
        key = canonical_incidence(diagram["P"], diagram["C"])
        orbits.setdefault(key, []).append(i)

    # Regression counts, not assumptions used to prune the enumeration.
    assert incidence_counts == Counter({0: 591, 1: 495})
    assert survivor_signatures == Counter({(0, (1, 4)): 1, (0, (1, 2, 2)): 6})
    assert len(survivors) == 7
    assert len(orbits) == 3
    assert sorted(map(len, orbits.values())) == [1, 2, 4]

    print("Normalized incidence counts (p=q, p!=q):",
          incidence_counts[0], incidence_counts[1])
    print("Incidence diagrams admitting a checked D:", len(survivors))
    print("B,C orbits under central permutations, duality, unordered top labels:",
          list(orbits.values()))
    print("Central sharing-component signatures:", dict(survivor_signatures))
    for number, indices in enumerate(orbits.values(), start=1):
        print("Orbit representative", number, json.dumps(survivors[indices[0]]))
    print("These are necessary-condition incidence survivors, not magma models.")


if __name__ == "__main__":
    main()

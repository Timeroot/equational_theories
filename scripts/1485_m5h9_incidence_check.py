#!/usr/bin/env python3
"""Exact central-incidence proof for n=24, r=3, m=5, h=9.

Enumerate graphs of co-occurring central predecessors, then exact covers
of the 5-by-5 central square by nine allowed rectangles. These are not
magma tables or SAT instances. See the accompanying research note for
the mathematical reduction. This is not a Lean theorem.
"""

from collections import Counter
from itertools import combinations, permutations


POINTS = tuple(range(5))
EDGES = tuple(combinations(POINTS, 2))
EDGE_INDEX = {edge: i for i, edge in enumerate(EDGES)}
SUBSETS = tuple(s for size in range(1, 4) for s in combinations(POINTS, size))
FULL_SQUARE = (1 << 25) - 1


def pair_mask(points):
    return sum(1 << EDGE_INDEX[pair] for pair in combinations(points, 2))


def graph_representatives():
    """All graph orbits, generated rather than supplied from a database."""
    edge_permutations = [
        tuple(EDGE_INDEX[tuple(sorted((p[a], p[b])))] for a, b in EDGES)
        for p in permutations(POINTS)
    ]
    remaining = set(range(1 << len(EDGES)))
    while remaining:
        graph = min(remaining)
        yield graph
        for p in edge_permutations:
            renamed = sum(1 << p[i] for i in range(len(EDGES)) if graph >> i & 1)
            remaining.discard(renamed)


def diagrams(graph):
    """All systems whose actual predecessor co-occurrence graph is graph.

    A rectangle's predecessor side is a clique and successor side an
    independent set. At each step the next uncovered cell is selected
    deterministically; every exact cover has exactly one rectangle there.
    The minimum-candidate choice changes only search order.
    """
    cliques = [s for s in SUBSETS if pair_mask(s) & graph == pair_mask(s)]
    independent = [s for s in SUBSETS if not pair_mask(s) & graph]
    rectangles = [
        (rows, cols, sum(1 << (5*i+j) for i in rows for j in cols), pair_mask(rows))
        for rows in cliques for cols in independent
    ]
    by_cell = [
        [i for i, (_, _, cells, _) in enumerate(rectangles) if cells >> cell & 1]
        for cell in range(25)
    ]

    def visit(covered, row_counts, col_counts, chosen, used_pairs):
        if len(chosen) == 9:
            if (covered == FULL_SQUARE and row_counts == [3]*5
                    and col_counts == [3]*5 and used_pairs == graph):
                yield tuple((rectangles[i][0], rectangles[i][1]) for i in chosen)
            return
        if covered == FULL_SQUARE:
            return
        remaining = 9 - len(chosen)
        if any(count > 3 or count + remaining < 3 for count in row_counts + col_counts):
            return
        candidates = None
        for cell in range(25):
            if covered >> cell & 1:
                continue
            possible = [
                i for i in by_cell[cell]
                if not covered & rectangles[i][2]
                and all(row_counts[j] < 3 for j in rectangles[i][0])
                and all(col_counts[j] < 3 for j in rectangles[i][1])
            ]
            if not possible:
                return
            if candidates is None or len(possible) < len(candidates):
                candidates = possible
        for i in candidates:
            rows, cols, cells, pairs = rectangles[i]
            new_rows, new_cols = row_counts.copy(), col_counts.copy()
            for j in rows:
                new_rows[j] += 1
            for j in cols:
                new_cols[j] += 1
            yield from visit(covered | cells, new_rows, new_cols,
                             chosen + [i], used_pairs | pairs)

    yield from visit(0, [0]*5, [0]*5, [], 0)


def profiles(rectangles):
    rows = [set(r) for r, _ in rectangles]
    cols = [set(c) for _, c in rectangles]
    central = [[len(c & r) for r in rows] for c in cols]
    assert all(entry in (0, 1) for row in central for entry in row)
    triples = tuple(combinations(range(9), 3))
    predecessors = [p for p in triples
                    if all(sum(z in rows[i] for i in p) == 1 for z in POINTS)]
    successors = [q for q in triples
                  if all(sum(z in cols[j] for j in q) == 1 for z in POINTS)]
    return [(p, q) for p in predecessors for q in successors
            if all(sum(central[i][j] for j in q) == 1 for i in p)
            and all(sum(central[i][j] for i in p) == 1 for j in q)]


def main():
    representatives = tuple(graph_representatives())
    assert len(representatives) == 34
    total = Counter()
    print("| Pair-graph mask | Diagrams with 0 / 1 / 2 admissible pairs |")
    print("| --- | --- |")
    for graph in representatives:
        histogram = Counter()
        for rectangle_system in diagrams(graph):
            count = len(profiles(rectangle_system))
            # Checked for each system, not inferred from the final summary.
            assert count <= 2, (graph, rectangle_system, count)
            histogram[count] += 1
        total.update(histogram)
        print(f"| {graph} | {histogram[0]} / {histogram[1]} / {histogram[2]} |", flush=True)
    print(f"Total diagrams: {sum(total.values())}; profile counts: {dict(sorted(total.items()))}")
    print("Every central diagram admits at most two degree-four profiles.")


if __name__ == "__main__":
    main()

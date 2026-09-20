#!/usr/bin/env python3
"""Finite central-incidence checks for r=3, m=4, h=9.

This enumerates incidence diagrams, not magma tables or an ATP problem.
The analytic proof reducing to these diagrams is separate. The output
is a reproducible finite check, not a Lean theorem.

The default mode is the degree-four profile bound used at order 24.
With --degree-five, check irregular least-degree-five profiles instead;
that lemma is independent of the total order and other degree classes.
"""

from collections import Counter
from itertools import combinations, permutations, product
import argparse


PAIRS = tuple(combinations(range(4), 2))
PERMUTATIONS = tuple(permutations(range(4)))


def valid(rectangles):
    # Each central row and column belongs to exactly three rectangles.
    if any(sum(i in rows for rows, _ in rectangles) != 3 for i in range(4)):
        return False
    if any(sum(j in cols for _, cols in rectangles) != 3 for j in range(4)):
        return False
    # At most one central middle between any two top vertices.
    return all(len(set(cols) & set(rows)) <= 1
               for _, cols in rectangles for rows, _ in rectangles)


def diagrams():
    # H has predecessor pair {0,1}. Its successor pair meets that pair
    # in zero or one points; these are representatives of the two orbits.
    for high_cols in ((2, 3), (0, 2)):
        remaining_cols = tuple(j for j in range(4) if j not in high_cols)
        for u0, u1, v0, v1 in product(PAIRS, repeat=4):
            rectangles = [((0, 1), high_cols), ((2,), u0), ((3,), u1),
                          (v0, (remaining_cols[0],)),
                          (v1, (remaining_cols[1],))]
            cells = [(i, j) for rows, cols in rectangles for i in rows for j in cols]
            if len(set(cells)) != 12:
                continue
            rectangles.extend(((i,), (j,)) for i in range(4) for j in range(4)
                              if (i, j) not in cells)
            if valid(rectangles):
                yield tuple(rectangles)


def canonical(rectangles):
    representatives = []
    for permutation in PERMUTATIONS:
        relabeled = tuple((tuple(sorted(permutation[i] for i in rows)),
                           tuple(sorted(permutation[j] for j in cols)))
                          for rows, cols in rectangles)
        representatives.append(tuple(sorted(relabeled)))
        representatives.append(tuple(sorted((cols, rows) for rows, cols in relabeled)))
    return min(representatives)


def profiles(rectangles):
    triples = tuple(combinations(range(9), 3))
    predecessors = [p for p in triples
                    if all(sum(i in rectangles[t][0] for t in p) == 1
                           for i in range(4))]
    successors = [q for q in triples
                  if all(sum(j in rectangles[t][1] for t in q) == 1
                         for j in range(4))]
    central = [[len(set(cols) & set(rows)) for rows, _ in rectangles]
               for _, cols in rectangles]
    return [(p, q) for p in predecessors for q in successors
            if all(sum(central[t][u] for u in q) == 1 for t in p)
            and all(sum(central[t][u] for t in p) == 1 for u in q)]


def degree_five_profiles(rectangles):
    """Irregular least-degree-five profiles and their good top pairs.

    A profile of size t has sharp degree 5-t. Its central-middle
    submatrix must have every row/column sum two. The size-two,
    sharp-regular profiles have no good top pairs and are omitted.
    """
    central = [[len(set(cols) & set(rows)) for rows, _ in rectangles]
               for _, cols in rectangles]
    result = []
    for size in (3, 4):
        subsets = tuple(combinations(range(9), size))
        predecessors = [p for p in subsets
                        if all(sum(i in rectangles[t][0] for t in p) == 1
                               for i in range(4))]
        successors = [q for q in subsets
                      if all(sum(j in rectangles[t][1] for t in q) == 1
                             for j in range(4))]
        for p, q in product(predecessors, successors):
            if (all(sum(central[t][u] for u in q) == 2 for t in p)
                    and all(sum(central[t][u] for t in p) == 2 for u in q)):
                good = frozenset((t, u) for t in p for u in q if not central[t][u])
                result.append((p, q, good))
    return result


def display(rectangles, admissible):
    # H = 2x2; A,B = 1x2; C,D = 2x1; 0,1,2,3 = singleton cells.
    alphabets = {(2, 2): iter("H"), (1, 2): iter("AB"),
                 (2, 1): iter("CD"), (1, 1): iter("0123")}
    labels = [next(alphabets[len(rows), len(cols)]) for rows, cols in rectangles]
    table = [[None] * 4 for _ in range(4)]
    for label, (rows, cols) in zip(labels, rectangles):
        for i in rows:
            for j in cols:
                assert table[i][j] is None
                table[i][j] = label
    encoded = "/".join("".join(row) for row in table)
    pairs = "; ".join("".join(sorted(labels[t] for t in p)) + "→" +
                      "".join(sorted(labels[t] for t in q)) for p, q in admissible)
    return encoded, pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="print all 88 representatives")
    parser.add_argument("--degree-five", action="store_true",
                        help="check the separate least-degree-five profile lemma")
    args = parser.parse_args()
    raw = list(diagrams())
    if args.degree_five:
        histogram = Counter()
        for rectangles in raw:
            admissible = degree_five_profiles(rectangles)
            histogram[len(admissible)] += 1
            assert all(len(p) == len(q) == 3 and len(good) == 3
                       for p, q, good in admissible)
            assert all(a[2] & b[2] for a, b in combinations(admissible, 2))
        assert len(raw) == 285
        assert histogram == Counter({0: 263, 1: 12, 2: 10})
        print("Least-degree-five profile lemma: all 285 diagrams checked.")
        print("Irregular profile counts:", dict(sorted(histogram.items())))
        print("Every profile has sharp degree two; any two share a good pair.")
        print("Hence at most one irregular least-degree-five vertex can occur.")
        return
    # The bound itself does not depend on canonicalization or its correctness.
    assert all(len(profiles(d)) <= 4 for d in raw)
    representatives = sorted({canonical(d) for d in raw})
    results = [(r, profiles(r)) for r in representatives]
    histogram = dict(sorted(Counter(len(p) for _, p in results).items()))
    print("Normalized labeled diagrams:", len(raw))
    print("Central relabeling + duality representatives:", len(representatives))
    print("Profile-count histogram:", histogram)
    print()
    print("| Central rectangle table | A1 profile pairs |")
    print("| --- | --- |")
    for rectangles, admissible in results:
        if admissible or args.all:
            table, pairs = display(rectangles, admissible)
            print(f"| `{table}` | `{pairs}` |" if pairs else f"| `{table}` | none |")


if __name__ == "__main__":
    main()

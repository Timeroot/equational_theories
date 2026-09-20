#!/usr/bin/env python3
"""Exact 16-bit graph lemma for the mixed A4 case at n=40,m=9,h=16.

See docs/1485_nine_central_sixteen_exclusion.md. These partial graphs
are NOT E1485 models. The proof enumerates every 4x4 zero-one matrix
and every permitted pair of four-bit boundary vectors, with no solver.
"""

from time import perf_counter


def sharp_tables():
    """Normalize two disjoint A3 predecessor pairs to {0,1},{2,3}."""
    for first in range(16):
        if first.bit_count() != 2:
            continue
        for second in range(16):
            if second.bit_count() != 2:
                continue
            rows = (first, first, second, second)
            columns = transpose(rows)
            deficits = tuple((2 if j == 0 else 1) - columns[j].bit_count() // 2
                             for j in range(4))
            # The unique low A4 target is the unique sharp-degree deficit.
            if sorted(deficits) == [0, 0, 0, 1]:
                yield first, second, deficits.index(1), rows, columns


def transpose(rows):
    return tuple(sum(((rows[i] >> j) & 1) << i for i in range(4))
                 for j in range(4))


def boundary_pairs(rows, columns, target):
    """The two exceptional high vertices have internal degree two."""
    for incoming in range(16):
        size = incoming.bit_count()
        if size > 2 or incoming & ~columns[target]:
            continue
        for outgoing in range(16):
            if outgoing.bit_count() == size and not outgoing & ~rows[0]:
                yield incoming, outgoing


def balanced(rows, columns, sharp_rows, sharp_columns, target, incoming, outgoing):
    for x in range(4):
        for y in range(4):
            if not (rows[x] >> y) & 1:
                continue
            predecessors = (columns[x] & sharp_columns[y]).bit_count()
            extensions = (rows[y] & sharp_rows[x]).bit_count()
            if y == target:
                predecessors += (incoming >> x) & 1
            if x == 0:
                extensions += (outgoing >> y) & 1
            if predecessors != extensions:
                return False
    return True


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: exact finite proof assertions are required.")
    started = perf_counter()
    tables = list(sharp_tables())
    expected = {(3, 5, 3): (21, 57), (3, 9, 2): (21, 57),
                (3, 12, 0): (24, 605), (5, 3, 3): (20, 25),
                (5, 9, 1): (20, 36), (5, 10, 0): (20, 88),
                (6, 9, 0): (17, 67), (9, 3, 2): (20, 25),
                (9, 5, 1): (20, 36), (9, 6, 0): (20, 88),
                (10, 5, 0): (17, 67), (12, 3, 0): (17, 38)}
    assert {(a, b, m) for a, b, m, _, _ in tables} == set(expected)
    maxima = [-1] * len(tables)
    survivors = [0] * len(tables)
    checked = 0
    attaining_fixture = False
    for mask in range(1 << 16):
        edge_count = mask.bit_count()
        # Low internal degrees are (3,4,4,4); the high vertices can
        # receive at most eight of these fifteen ordinary edges.
        if edge_count < 7:
            continue
        rows = tuple((mask >> (4*i)) & 15 for i in range(4))
        columns = transpose(rows)
        if rows[0].bit_count() > 3 or columns[0].bit_count() > 3:
            continue
        squares = tuple(tuple((rows[i] & columns[j]).bit_count()
                              for j in range(4)) for i in range(4))
        for index, (first, second, target, sharp_rows, sharp_columns) in enumerate(tables):
            if any(squares[i][j] > 1 and not (sharp_rows[i] >> j) & 1
                   for i in range(4) for j in range(4)):
                continue
            bad = sum(squares[i][j] for i in range(4) for j in range(4)
                      if (sharp_rows[i] >> j) & 1)
            for incoming, outgoing in boundary_pairs(rows, columns, target):
                checked += 1
                if not balanced(rows, columns, sharp_rows, sharp_columns,
                                target, incoming, outgoing):
                    continue
                tau = bad + 15 - edge_count + incoming.bit_count()
                assert tau <= 24, (mask, first, second, target, incoming, outgoing, tau)
                maxima[index] = max(maxima[index], tau)
                survivors[index] += 1
                if (mask, first, second, incoming, outgoing) == (13261, 3, 12, 1, 1):
                    assert tau == 24
                    attaining_fixture = True
    for index, (first, second, target, _, _) in enumerate(tables):
        result = (maxima[index], survivors[index])
        assert result == expected[first, second, target]
        print(f"Q=({first:04b},{second:04b}), target={target}: "
              f"maximum={result[0]}, partial fixtures={result[1]}")
    assert checked == 160508 and sum(survivors) == 1189 and attaining_fixture
    print(f"Mixed A4 lemma VERIFIED: tau_low <= 24 < 25; "
          f"{checked} boundary pairs checked in {perf_counter()-started:.3f}s.")


if __name__ == "__main__":
    main()

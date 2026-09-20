#!/usr/bin/env python3
"""Exact sixteen-bit incidence exclusion; see the matching research note.

No SAT/SMT solver or floating-point arithmetic is used. The partial incidence
fixtures accepted here are necessary-data fixtures, not E1485 magmas.
"""

import argparse
from itertools import combinations, product
from time import perf_counter


def normalized_cases():
    """The A3 source pairs are 01,23 and the exceptional vertex is 0."""
    pairs = list(combinations(range(4), 2))
    result = []
    for first, second in product(pairs, repeat=2):
        used = [int(i in first) + int(i in second) for i in range(4)]
        deficit = [(2 if i == 0 else 1) - used[i] for i in range(4)]
        if sorted(deficit) != [0, 0, 0, 1]:
            continue
        target = deficit.index(1)
        first_mask = sum(1 << i for i in first)
        second_mask = sum(1 << i for i in second)
        if first_mask & (1 << target):
            continue  # The A4 pair must not already have an A3 product.
        sharp = (first_mask | (1 << target), first_mask,
                 second_mask, second_mask)
        result.append((first, second, target, sharp))
    assert len(result) == 9
    assert len({case[3] for case in result}) == 9
    return result


def columns(rows):
    return tuple(sum(((rows[i] >> j) & 1) << i for i in range(4))
                 for j in range(4))


def value(rows, sharp, sharp_columns):
    """Return tau_low, or None if a necessary incidence condition fails."""
    edges = sum(row.bit_count() for row in rows)
    if not 7 <= edges <= 15 or rows[0].bit_count() > 3:
        return None
    cols = columns(rows)
    if cols[0].bit_count() > 3:
        return None
    bad = 0
    for x in range(4):
        for y in range(4):
            if not ((sharp[x] >> y) & 1):
                if (rows[x] & cols[y]).bit_count() > 1:
                    return None
            if (rows[x] >> y) & 1:
                eta = (cols[x] & sharp_columns[y]).bit_count()
                beta = (sharp[x] & rows[y]).bit_count()
                if eta != beta or eta > 3:
                    return None
                bad += eta
    return bad + 15 - edges


def reference_value(rows, sharp):
    """Independent set/triple formulation for deterministic spot checks."""
    ordinary = {(i, j) for i in range(4) for j in range(4)
                if rows[i] & (1 << j)}
    replacement = {(i, j) for i in range(4) for j in range(4)
                   if sharp[i] & (1 << j)}
    if not 7 <= len(ordinary) <= 15:
        return None
    if sum(i == 0 for i, _ in ordinary) > 3:
        return None
    if sum(j == 0 for _, j in ordinary) > 3:
        return None
    for x, y in product(range(4), repeat=2):
        count = sum((x, z) in ordinary and (z, y) in ordinary
                    for z in range(4))
        if count > 1 and (x, y) not in replacement:
            return None
    for x, y in ordinary:
        eta = sum((z, x) in ordinary and (z, y) in replacement
                  for z in range(4))
        beta = sum((y, z) in ordinary and (x, z) in replacement
                   for z in range(4))
        if eta != beta or eta > 3:
            return None
    bad = sum((x, y) in ordinary and (y, z) in ordinary
              and (x, z) in replacement
              for x, y, z in product(range(4), repeat=3))
    return bad + 15 - len(ordinary)


def main():
    if not __debug__:
        raise SystemExit("Run without python -O: proof checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-audit", type=int, default=128,
                        help="accepted and regularly spaced masks to cross-check per case")
    args = parser.parse_args()
    if args.reference_audit < 0:
        parser.error("--reference-audit must be nonnegative")

    # A genuine positive control for the NECESSARY INCIDENCE SYSTEM only.
    fixture_sharp, fixture_rows = (7, 3, 9, 9), (7, 3, 12, 1)
    assert value(fixture_rows, fixture_sharp, columns(fixture_sharp)) == 20
    assert reference_value(fixture_rows, fixture_sharp) == 20
    assert value((15, 15, 15, 15), fixture_sharp,
                 columns(fixture_sharp)) is None

    start = perf_counter()
    total = 0
    maximum = -1
    expected = {
        ((0, 1), (0, 2), 3): (16, 8, 20),
        ((0, 1), (0, 3), 2): (16, 8, 20),
        ((0, 2), (0, 1), 3): (5, 7, 18),
        ((0, 2), (0, 3), 1): (10, 8, 19),
        ((0, 3), (0, 1), 2): (5, 7, 18),
        ((0, 3), (0, 2), 1): (10, 8, 19),
        ((1, 2), (0, 3), 0): (35, 8, 18),
        ((1, 3), (0, 2), 0): (35, 8, 18),
        ((2, 3), (0, 1), 0): (20, 8, 17),
    }
    assert {(first, second, target) for first, second, target, _ in normalized_cases()} == set(expected)
    for first, second, target, sharp in normalized_cases():
        sharp_columns = columns(sharp)
        accepted = 0
        local_max = -1
        max_edges = -1
        stride = max(1, 65536 // max(1, args.reference_audit))
        for mask in range(65536):
            rows = tuple((mask >> (4 * i)) & 15 for i in range(4))
            answer = value(rows, sharp, sharp_columns)
            audit = args.reference_audit and (
                mask % stride == 0 or
                (answer is not None and accepted < args.reference_audit))
            if audit:
                assert answer == reference_value(rows, sharp)
            if answer is None:
                continue
            accepted += 1
            local_max = max(local_max, answer)
            max_edges = max(max_edges, sum(row.bit_count() for row in rows))
            assert answer < 25, (first, second, target, rows, answer)
        assert accepted > 0  # Each normalized case has a partial-data control.
        assert (accepted, max_edges, local_max) == expected[first, second, target]
        print(f"first={first} second={second} A4_target={target}: "
              f"accepted={accepted}, max_edges={max_edges}, max_tau={local_max}")
        maximum = max(maximum, local_max)
        total += accepted
    assert maximum == 20 and total == 152
    print(f"PASS: 9 * 65536 masks; {total} accepted partial incidences; "
          f"max_tau={maximum}; {perf_counter() - start:.3f}s")


if __name__ == "__main__":
    main()

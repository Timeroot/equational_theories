#!/usr/bin/env python3
"""Construct central towers of cross-inverse loops and check finite instances.

See docs/cross-inverse-loop-towers.md for the general research proof. These
checks are not Lean certificates and do not change catalogue proof statuses.
Only loop tables are built, never the Cartesian-square division tables.
"""

import argparse
from collections import Counter
import json
from pathlib import Path

import numpy as np


def cycles(permutation):
    """Enumerate the cycles, checking that every traversal closes at its start."""
    seen = np.zeros(len(permutation), dtype=bool)
    for start in range(len(permutation)):
        if seen[start]:
            continue
        cycle, x = [], start
        while not seen[x]:
            seen[x] = True
            cycle.append(x)
            x = int(permutation[x])
        assert x == start
        yield cycle


def check(table, inverse, grade, prime, period):
    """Independently check the complete loop and the induction invariant."""
    n = len(inverse)
    points = np.arange(n)
    assert table.shape == (n, n)
    assert np.all((0 <= table) & (table < n))
    assert np.array_equal(table[0], points)
    assert np.array_equal(table[:, 0], points)
    assert np.array_equal(np.sort(inverse), points)
    assert np.all(np.sort(table, axis=0) == points[:, None])
    assert np.all(np.sort(table, axis=1) == points[None, :])
    assert np.all(table[table, inverse[:, None]] == points[None, :])
    assert np.all(inverse[table] == table[inverse[:, None], inverse[None, :]])
    assert np.all(grade[table] == (grade[:, None] + grade[None, :]) % prime)
    assert np.array_equal(np.unique(grade), np.arange(prime))
    assert np.all(grade[inverse] == -grade % prime)
    assert np.flatnonzero(inverse == points).tolist() == [0]
    assert np.all(inverse[inverse[grade == 0]] == points[grade == 0])
    profile = Counter()
    nonzero_cycles = 0
    for cycle in cycles(inverse):
        assert period % len(cycle) == 0
        if grade[cycle[0]]:
            assert len(cycle) == period
            nonzero_cycles += 1
        profile[len(cycle)] += 1
    assert nonzero_cycles == (prime - 1) // 2
    assert max(profile) == period
    return dict(sorted(profile.items()))


def lift(table, inverse, grade, prime, period):
    """Solve offsets by twisted cycles and build the next central extension."""
    n = len(inverse)
    diagonal = np.zeros(n, dtype=np.int64)
    for cycle in cycles(inverse):
        if grade[cycle[0]]:
            assert len(cycle) == period
            diagonal[cycle[0]] = grade[cycle[0]]

    # T(x,y) = (x*y,Jx); pairs are encoded by n*x+y.
    twist = (table * n + inverse[:, None]).ravel()
    offset = np.zeros(n * n, dtype=np.int64)
    for cycle in cycles(twist):
        unit_index = next((i for i, pair in enumerate(cycle)
                           if pair // n == 0 or pair % n == 0), None)
        if unit_index is not None:
            cycle = cycle[unit_index:] + cycle[:unit_index]
        value = 0
        for pair in cycle:
            x, _ = divmod(pair, n)
            offset[pair] = value
            value = (int(diagonal[x]) - value) % prime
        assert value == 0, "The offset recurrence did not close"

    offset = offset.reshape(n, n)
    assert not np.any(offset[0]) and not np.any(offset[:, 0])
    assert np.all((offset + offset[table, inverse[:, None]]) % prime
                  == diagonal[:, None])
    assert np.all(offset[np.arange(n), inverse] == diagonal)

    # Check the alternating trace independently of the larger table.
    trace = np.zeros(n, dtype=np.int64)
    current = np.arange(n)
    for i in range(period):
        trace = (trace + (-1 if i % 2 else 1) * diagonal[current]) % prime
        current = inverse[current]
    assert np.all(trace == grade)

    points = np.arange(n * prime)
    base, fibre = points // prime, points % prime
    enlarged = table[base[:, None], base[None, :]] * prime + (
        fibre[:, None] + fibre[None, :] + offset[base[:, None], base[None, :]]
    ) % prime
    lifted_inverse = inverse[base] * prime + (-fibre - diagonal[base]) % prime
    return enlarged, lifted_inverse, grade[base], np.flatnonzero(diagonal).tolist()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=5)
    parser.add_argument("--levels", type=int, default=3,
                        help="Number of extensions; the initial loop has order p")
    parser.add_argument("--output", type=Path,
                        help="Save a small research-check summary, not the tables")
    args = parser.parse_args()
    p = args.prime
    if p <= 3 or any(p % d == 0 for d in range(2, int(p ** 0.5) + 1)):
        parser.error("--prime must be a prime greater than three")
    if args.levels < 0:
        parser.error("--levels must be nonnegative")

    table = np.add.outer(np.arange(p), np.arange(p)) % p
    inverse = -np.arange(p) % p
    grade = np.arange(p)
    period, support, records = 2, [], []
    for level in range(args.levels + 1):
        if level:
            table, inverse, grade, support = lift(table, inverse, grade, p, period)
            period *= p
        profile = check(table, inverse, grade, p, period)
        record = {"level": level, "loop_order": len(inverse),
                  "inverse_order": period, "inverse_cycles": profile,
                  "diagonal_support_in_base": support,
                  "division_order_by_construction": len(inverse) ** 2,
                  "turn_order_by_construction": 2 * period}
        records.append(record)
        print(json.dumps(record), flush=True)
    if args.output:
        args.output.write_text(json.dumps({
            "status": "Python research check; general tower existence awaiting Lean",
            "prime": p, "levels": records,
            "proof": "docs/cross-inverse-loop-towers.md",
            "catalogue_rows_closed": 0,
        }, indent=2) + "\n")


if __name__ == "__main__":
    main()

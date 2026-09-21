#!/usr/bin/env python3
"""Tiny exhaustive graph lemma for the remaining nine-central K=15 case.

Standard library only.  This checks a necessary seven-vertex graph system,
not complete magma tables.
"""

import argparse
import sys
from itertools import permutations, product
from time import perf_counter


N = 7
DEGREES = (3, 2, 2, 2, 2, 2, 2)
FIXTURE_Q = (1, 2, 3, 4, 5, 6, 0)
FIXTURE_ROWS = (69, 9, 18, 36, 72, 17, 34)
BAD_WALK = (0, 0, 2, 1, 0)


def partitions(n, lo=1):
    if n == 0:
        yield ()
    for first in range(lo, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def normalized_cases():
    for first in range(2, N + 1):
        for rest in partitions(N - first):
            lengths = (first,) + rest
            reps = list(range(first))
            start, previous = first, None
            for length in rest:
                if length != previous:
                    reps.append(start)
                start += length
                previous = length
            for a in reps:
                yield lengths, a


def permutation_from_lengths(lengths):
    q, start = [], 0
    for length in lengths:
        q.extend(start + (i + 1) % length for i in range(length))
        start += length
    return tuple(q)


def canonical_pair(q, a):
    """Independent cycle traversal used only for the normalization control."""
    seen, cycles = set(), []
    for start in range(N):
        if start in seen:
            continue
        cycle, x = [], start
        while x not in seen:
            cycle.append(x)
            seen.add(x)
            x = q[x]
        cycles.append(cycle)
    first = cycles.pop(0)  # The traversal starts at the distinguished vertex 0.
    cycles.sort(key=lambda c: (len(c), a not in c, min(c)))
    for i, cycle in enumerate(cycles):
        if a in cycle:
            shift = cycle.index(a)
            cycles[i] = cycle[shift:] + cycle[:shift]
    order = first + [x for cycle in cycles for x in cycle]
    inverse = {x: i for i, x in enumerate(order)}
    lengths = (len(first),) + tuple(map(len, cycles))
    relabeled = tuple(inverse[q[x]] for x in order)
    assert relabeled == permutation_from_lengths(lengths)
    return lengths, inverse[a]


def literal_evaluate(q, rows):
    """Set-based evaluator, independent of orbit construction and bit pruning."""
    edges = {(x, y) for x in range(N) for y in range(N)
             if (rows[x] // (2 ** y)) % 2}
    qi = tuple(q.index(x) for x in range(N))
    outgoing = tuple(sum(x == v for x, y in edges) for v in range(N))
    incoming = tuple(sum(y == v for x, y in edges) for v in range(N))
    margins = outgoing == incoming == DEGREES
    two_steps = {(x, y): sum((x, z) in edges and (z, y) in edges
                            for z in range(N))
                 for x in range(N) for y in range(N)}
    repeated = all(count <= 1 for (x, y), count in two_steps.items()
                   if y != q[x])
    eta_zero = {(x, y) for x, y in edges if (qi[y], x) not in edges}
    beta_zero = {(x, y) for x, y in edges if (y, q[x]) not in edges}
    defect = (len(eta_zero) == len(beta_zero) == 1
              and next(iter(eta_zero))[1] == 0
              and next(iter(beta_zero))[0] == 0
              and next(iter(eta_zero))[0] == next(iter(beta_zero))[1])
    forbidden_shift = all((x, qi[qi[x]]) not in edges for x in range(N))
    one_a = all((q[x] == z) == (q[y] == w)
                for x, y, z, w in product(range(N), repeat=4)
                if (x, y) in edges and (y, z) in edges
                and (z, w) in edges and q[w] == x)
    bad_walks = []
    for walk in product(range(N), repeat=5):
        if all((walk[i], walk[(i + 1) % 5]) in edges for i in range(5)):
            bad_count = sum(q[walk[i]] == walk[(i + 2) % 5]
                            for i in range(5))
            if bad_count == 1:
                bad_walks.append(walk)
    return {
        'margins': margins,
        'repeated': repeated,
        'defect': defect,
        'forbidden_shift': forbidden_shift,
        'one_a': one_a,
        'bad_walks': tuple(bad_walks),
    }


def search_case(lengths, a):
    q = permutation_from_lengths(lengths)
    qi = tuple(q.index(x) for x in range(N))
    phi = lambda xy: (qi[xy[1]], xy[0])
    forbidden = {(x, qi[qi[x]]) for x in range(N)}
    f, e = (0, a), (a, 0)
    segment, current = [], f
    while current not in segment:
        segment.append(current)
        if current == e:
            break
        current = phi(current)
    if segment[-1] != e or phi(e) in segment or set(segment) & forbidden:
        return 0, []

    orbit_f, current = set(), f
    while current not in orbit_f:
        orbit_f.add(current)
        current = phi(current)
    seen, optional = set(orbit_f), []
    for xy in product(range(N), repeat=2):
        if xy in seen:
            continue
        orbit, current = [], xy
        while current not in orbit:
            orbit.append(current)
            current = phi(current)
        seen.update(orbit)
        if not set(orbit) & forbidden:
            optional.append(orbit)

    rows, cols = [0] * N, [0] * N
    nodes, complete = 0, []

    def insert(edges):
        for x, y in edges:
            rows[x] |= 1 << y
            cols[y] |= 1 << x

    def remove(edges):
        # Distinct phi orbits are disjoint, so XOR removes exactly this orbit.
        for x, y in edges:
            rows[x] ^= 1 << y
            cols[y] ^= 1 << x

    def valid_partial():
        if any(rows[x].bit_count() > DEGREES[x]
               or cols[x].bit_count() > DEGREES[x] for x in range(N)):
            return False
        return all((rows[x] & cols[y]).bit_count() <= 1
                   for x in range(N) for y in range(N) if y != q[x])

    def search(active):
        nonlocal nodes
        nodes += 1
        deficits = [DEGREES[x] - rows[x].bit_count() for x in range(N)]
        if not any(deficits):
            if all(cols[x].bit_count() == DEGREES[x] for x in range(N)):
                complete.append((q, tuple(rows)))
            return
        # Pick an unmet row. In any extension, it has a first selected orbit
        # in the following fixed order; branch on exactly that choice.
        options = [[i for i in sorted(active)
                    if any(x == r for x, _ in optional[i])]
                   for r in range(N)]
        r = min((x for x in range(N) if deficits[x]),
                key=lambda x: len(options[x]))
        remaining = set(active)
        for i in options[r]:
            remaining.remove(i)
            insert(optional[i])
            if valid_partial():
                search(remaining)
            remove(optional[i])

    insert(segment)
    if valid_partial():
        search(set(range(len(optional))))
    return nodes, complete


def main():
    if sys.flags.optimize:
        raise SystemExit('Run without -O: this checker requires its assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verbose', action='store_true')
    args = parser.parse_args()
    begin = perf_counter()
    cases = tuple(normalized_cases())
    assert len(cases) == len(set(cases)) == 90

    # Check the proposed normalization for every labeled permutation moving
    # the distinguished vertex 0, and every choice of a.
    normalization_checks = 0
    for q in permutations(range(N)):
        if q[0] == 0:
            continue
        for a in range(N):
            assert canonical_pair(q, a) in cases
            normalization_checks += 1
    assert normalization_checks == 30240

    fixture = literal_evaluate(FIXTURE_Q, FIXTURE_ROWS)
    assert all(fixture[key] for key in
               ('margins', 'repeated', 'defect', 'forbidden_shift', 'one_a'))
    assert BAD_WALK in fixture['bad_walks']
    damaged_rows = list(FIXTURE_ROWS)
    damaged_rows[0] ^= 1  # Delete its loop: the positive control must then fail.
    damaged = literal_evaluate(FIXTURE_Q, tuple(damaged_rows))
    assert not damaged['margins'] and not damaged['defect']

    nodes, complete = 0, []
    for lengths, a in cases:
        count, found = search_case(lengths, a)
        nodes += count
        complete.extend(found)
        if args.verbose:
            print(lengths, 'a=', a, 'nodes=', count, 'complete=', len(found))

    assert complete == [(FIXTURE_Q, FIXTURE_ROWS)], complete
    assert nodes == 79, nodes
    for q, rows in complete:
        checked = literal_evaluate(q, rows)
        assert all(checked[key] for key in
                   ('margins', 'repeated', 'defect', 'forbidden_shift', 'one_a'))
        assert checked['bad_walks']
    print(f'PASS: {normalization_checks} normalization controls; '
          f'{len(cases)} cases; {nodes} search nodes; '
          'one intermediate graph, rejected by a literal five-walk.')
    print(f'Elapsed: {perf_counter() - begin:.3f} seconds')


if __name__ == '__main__':
    main()

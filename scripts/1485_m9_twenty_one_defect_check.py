#!/usr/bin/env python3
"""Exact partial-orbit check for K=20, tau=19 on seven B vertices.

Necessary graph incidences only, not magma enumeration. No SAT solver.
The first cycle has the unique degree descent at vertex zero; all other
cycles are homogeneous. Its unique partial phi-orbit is specified exactly.
See docs/1485_order_forty_nine_central_twenty_one_defect.md.
"""

import argparse
from itertools import permutations, product
from time import perf_counter


N = 7
FIXTURE_DEGREES = (3, 2, 2, 2, 2, 2, 2)
FIXTURE_ROWS = (69, 9, 18, 36, 72, 17, 34)
EXPECTED = {
    (2, 3, 3, 3, 3, 3, 3): [90, 72, 0],
    (2, 2, 3, 3, 3, 3, 4): [154, 291, 0],
    (2, 2, 2, 3, 3, 4, 4): [152, 313, 0],
}


def partitions(n, low=1):
    if n == 0:
        yield ()
    for first in range(low, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def permutation_from_lengths(lengths):
    q, start = [], 0
    for length in lengths:
        q.extend(start + (i + 1) % length for i in range(length))
        start += length
    return tuple(q)


def normalized_cases():
    for fours in range(4):
        inventory = {2: 1 + fours, 3: 6 - 2 * fours, 4: fours}
        for length in range(2, N + 1):
            for end_low in range(1, length):
                for low in (2, 3):
                    first_degrees = (low + 1,) + (low,) * end_low
                    first_degrees += (low + 1,) * (length - end_low - 1)
                    rest = {d: inventory[d] - first_degrees.count(d)
                            for d in (2, 3, 4)}
                    if min(rest.values()) < 0:
                        continue
                    for shapes in product(*(tuple(partitions(rest[d])) for d in (2, 3, 4))):
                        cycles = tuple((d, size) for d, shape in zip((2, 3, 4), shapes)
                                       for size in shape)
                        degrees = first_degrees + tuple(d for d, size in cycles
                                                         for _ in range(size))
                        lengths = (length,) + tuple(size for d, size in cycles)
                        representatives = list(range(length))
                        start, previous = length, None
                        for cycle in cycles:
                            if cycle != previous:
                                representatives.append(start)
                            start += cycle[1]
                            previous = cycle
                        for c in representatives:
                            yield degrees, lengths, c


def search_case(degrees, lengths, c):
    q = permutation_from_lengths(lengths)
    qi = tuple(q.index(x) for x in range(N))
    delta = tuple(degrees[x] - degrees[q[x]] for x in range(N))
    assert delta[0] == 1 and delta.count(-1) == 1 and delta.count(0) == 5
    s = delta.index(-1)
    phi = lambda xy: (qi[xy[1]], xy[0])
    f, e = (0, c), (c, q[s])
    forbidden = {(x, qi[qi[x]]) for x in range(N)}

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
        if not forbidden.intersection(orbit):
            optional.append(orbit)

    rows, cols = [0] * N, [0] * N
    nodes, complete = 0, []

    def insert(edges):
        for x, y in edges:
            rows[x] |= 1 << y
            cols[y] |= 1 << x

    def remove(edges):
        for x, y in edges:
            rows[x] ^= 1 << y
            cols[y] ^= 1 << x

    def valid():
        if any(rows[x].bit_count() > degrees[x]
               or cols[x].bit_count() > degrees[x] for x in range(N)):
            return False
        return all((rows[x] & cols[y]).bit_count() <= 1
                   for x in range(N) for y in range(N) if y != q[x])

    def search(active):
        nonlocal nodes
        nodes += 1
        deficits = [degrees[x] - rows[x].bit_count() for x in range(N)]
        if not any(deficits):
            if all(cols[x].bit_count() == degrees[x] for x in range(N)):
                complete.append(tuple(rows))
            return
        options = [[i for i in sorted(active) if any(x == r for x, y in optional[i])]
                   for r in range(N)]
        r = min((x for x in range(N) if deficits[x]), key=lambda x: len(options[x]))
        remaining = set(active)
        for i in options[r]:
            remaining.remove(i)
            insert(optional[i])
            if valid():
                search(remaining)
            remove(optional[i])

    insert(segment)
    if valid():
        search(set(range(len(optional))))
    return nodes, complete


def canonical_case(q, degrees, c):
    """Independent explicit relabeling, with the unique descent at zero."""
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
    first = cycles.pop(0)
    cycles.sort(key=lambda cycle: (degrees[cycle[0]], len(cycle), c not in cycle,
                                    min(cycle)))
    for i, cycle in enumerate(cycles):
        assert len({degrees[x] for x in cycle}) == 1
        if c in cycle:
            shift = cycle.index(c)
            cycles[i] = cycle[shift:] + cycle[:shift]
    order = first + [x for cycle in cycles for x in cycle]
    inverse = {x: i for i, x in enumerate(order)}
    lengths = (len(first),) + tuple(map(len, cycles))
    assert tuple(inverse[q[x]] for x in order) == permutation_from_lengths(lengths)
    return tuple(degrees[x] for x in order), lengths, inverse[c]


def normalization_controls(cases):
    degree_options = [degrees for degrees in product((2, 3, 4), repeat=N)
                      if sum(degrees) == 20]
    count = 0
    for q in permutations(range(N)):
        if q[0] == 0:
            continue
        for degrees in degree_options:
            delta = tuple(degrees[x] - degrees[q[x]] for x in range(N))
            if delta[0] != 1 or delta.count(-1) != 1 or delta.count(0) != 5:
                continue
            for c in range(N):
                assert canonical_case(q, degrees, c) in cases
                count += 1
    return count


def literal_evaluate(degrees, q, rows):
    """Independent sets verify the search's positive and negative fixtures."""
    edges = {(x, y) for x, y in product(range(N), repeat=2)
             if (rows[x] // (2 ** y)) % 2}
    qi = tuple(q.index(x) for x in range(N))
    rotated = {(qi[y], x) for x, y in edges}
    outgoing = tuple(sum((x, y) in edges for y in range(N)) for x in range(N))
    incoming = tuple(sum((y, x) in edges for y in range(N)) for x in range(N))
    repeated = all(sum((x, z) in edges and (z, y) in edges for z in range(N)) <= 1
                   for x, y in product(range(N), repeat=2) if y != q[x])
    return {
        "margins": outgoing == incoming == degrees,
        "defect": len(edges - rotated) == len(rotated - edges) == 1,
        "repeated": repeated,
        "shift": all((x, qi[qi[x]]) not in edges for x in range(N)),
    }


def main():
    if not __debug__:
        raise SystemExit("Run without python -O: this checker needs its assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    started = perf_counter()
    cases = tuple(normalized_cases())
    assert len(cases) == len(set(cases)) == 396
    controls = normalization_controls(set(cases))
    assert controls == 141120

    # The same partial-orbit search must retain the known K=15 positive
    # incidence fixture; it fails the all-B five-cycle rule, not this search.
    fixture_nodes, fixture = search_case(FIXTURE_DEGREES, (7,), 0)
    assert fixture == [FIXTURE_ROWS] and fixture_nodes > 0
    fixture_q = permutation_from_lengths((7,))
    assert all(literal_evaluate(FIXTURE_DEGREES, fixture_q, FIXTURE_ROWS).values())
    damaged = list(FIXTURE_ROWS)
    damaged[0] ^= 1  # Removing its loop repairs the rotation but breaks degrees.
    checked = literal_evaluate(FIXTURE_DEGREES, fixture_q, tuple(damaged))
    assert not checked["margins"] and not checked["defect"]

    by_profile = {}
    total_nodes = total_complete = 0
    for degrees, lengths, c in cases:
        nodes, complete = search_case(degrees, lengths, c)
        profile = tuple(sorted(degrees))
        tally = by_profile.setdefault(profile, [0, 0, 0])
        tally[0] += 1
        tally[1] += nodes
        tally[2] += len(complete)
        total_nodes += nodes
        total_complete += len(complete)
        if args.verbose or complete:
            print(degrees, lengths, c, "nodes=", nodes, "complete=", complete)
    assert by_profile == EXPECTED
    assert (total_nodes, total_complete) == (676, 0)
    for profile, counts in sorted(by_profile.items()):
        print(profile, "cases/nodes/complete=", counts)
    print(f"PASS: normalization controls={controls}; cases={len(cases)}; "
          f"nodes={total_nodes}; complete={total_complete}; "
          f"elapsed={perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()

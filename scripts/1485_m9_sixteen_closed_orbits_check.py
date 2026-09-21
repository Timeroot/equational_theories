#!/usr/bin/env python3
"""Check the 24 closed-edge-rotation K=16 leaf cases, using no SAT solver.

Only standard-library modules and two elementary helpers from the adjacent
fifteen-edge checker are used. No magma tables are enumerated.
"""

import argparse
import importlib.util
import sys
from itertools import permutations, product
from pathlib import Path
from time import perf_counter

helper_path = Path(__file__).with_name('1485_m9_fifteen_edges_check.py')
spec = importlib.util.spec_from_file_location('fifteen_edge_helpers', helper_path)
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)

PROFILES = ((1, 2, 2, 2, 3, 3, 3),
            (1, 2, 2, 2, 2, 3, 4),
            (1, 1, 2, 3, 3, 3, 3))
EXPECTED = ((9, 2104, 93), (5, 1922, 42), (10, 1052, 0))
FIXTURE_Q = tuple(range(7))
FIXTURE_ROWS = (64, 12, 18, 34, 100, 88, 49)


def q_options(degrees):
    groups = [(d, degrees.count(d)) for d in sorted(set(degrees))]
    for shapes in product(*(list(helpers.partitions(count)) for d, count in groups)):
        lengths = tuple(length for shape in shapes for length in shape)
        yield shapes, helpers.permutation_from_lengths(lengths)


def literal_evaluate(degrees, q, rows):
    """Direct sets, ordinary integer counts, and literal closed five-walks."""
    edges = {(x, y) for x in range(7) for y in range(7)
             if (rows[x] // (2 ** y)) % 2}
    out = [{y for a, y in edges if a == x} for x in range(7)]
    incoming = [{x for x, b in edges if b == y} for y in range(7)]
    qi = tuple(q.index(x) for x in range(7))
    margins = (tuple(map(len, out)) == degrees
               and tuple(map(len, incoming)) == degrees)
    rotation = {(qi[y], x) for x, y in edges} == edges
    repeated = all(len(out[x].intersection(incoming[y])) <= 1
                   for x in range(7) for y in range(7) if y != q[x])
    shift = all((x, qi[qi[x]]) not in edges for x in range(7) if degrees[x] >= 2)
    one_a = all((q[x] == z) == (q[y] == w)
                for x in range(7) for y in out[x] for z in out[y] for w in out[z]
                if q[w] == x)
    bad_walk = None
    # Enumerate actual walks with sets, independently of the bit-mask search.
    for x in range(7):
        for y in out[x]:
            for z in out[y]:
                for w in out[z]:
                    for v in out[w]:
                        if x not in out[v]:
                            continue
                        walk = (x, y, z, w, v)
                        bad = sum(q[walk[i]] == walk[(i + 2) % 5] for i in range(5))
                        if bad == 1:
                            bad_walk = walk
                            break
    return margins, rotation, repeated, shift, one_a, bad_walk


def search_case(degrees, q):
    qi = tuple(q.index(x) for x in range(7))
    phi = lambda xy: (qi[xy[1]], xy[0])
    forbidden = {(x, qi[qi[x]]) for x in range(7) if degrees[x] >= 2}
    seen, orbits = set(), []
    for xy in product(range(7), repeat=2):
        if xy in seen:
            continue
        orbit, current = [], xy
        while current not in orbit:
            orbit.append(current)
            current = phi(current)
        seen.update(orbit)
        if not forbidden.intersection(orbit):
            orbits.append(orbit)

    rows, cols = [0] * 7, [0] * 7
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
        return (all(rows[x].bit_count() <= degrees[x]
                    and cols[x].bit_count() <= degrees[x] for x in range(7))
                and all((rows[x] & cols[y]).bit_count() <= 1
                        for x in range(7) for y in range(7) if y != q[x]))

    def search(active):
        nonlocal nodes
        nodes += 1
        deficits = [degrees[x] - rows[x].bit_count() for x in range(7)]
        if not any(deficits):
            if all(cols[x].bit_count() == degrees[x] for x in range(7)):
                complete.append(tuple(rows))
            return
        options = [[i for i in sorted(active) if any(x == r for x, y in orbits[i])]
                   for r in range(7)]
        r = min((x for x in range(7) if deficits[x]), key=lambda x: len(options[x]))
        remaining = set(active)
        for i in options[r]:
            remaining.remove(i)
            insert(orbits[i])
            if valid():
                search(remaining)
            remove(orbits[i])

    search(set(range(len(orbits))))
    return nodes, complete


def normalization_control(degrees):
    """All labeled degree-preserving permutations have a listed cycle type."""
    listed = {shape for shape, q in q_options(degrees)}
    groups = [tuple(x for x in range(7) if degrees[x] == d)
              for d in sorted(set(degrees))]
    count = 0
    for images in product(*(list(permutations(group)) for group in groups)):
        q = list(range(7))
        for group, image in zip(groups, images):
            for x, y in zip(group, image):
                q[x] = y
        shapes = []
        for group in groups:
            visited, sizes = set(), []
            for x in group:
                if x in visited:
                    continue
                size = 0
                while x not in visited:
                    visited.add(x)
                    size += 1
                    x = q[x]
                sizes.append(size)
            shapes.append(tuple(sorted(sizes)))
        assert tuple(shapes) in listed
        count += 1
    return count


def main():
    if sys.flags.optimize:
        raise SystemExit('Run without -O: this checker requires its assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verbose', action='store_true')
    args = parser.parse_args()
    begin = perf_counter()

    good = literal_evaluate(PROFILES[0], FIXTURE_Q, FIXTURE_ROWS)
    assert all(good[:5]) and good[5] is not None
    bad_rows = list(FIXTURE_ROWS)
    bad_rows[0] = 0
    bad = literal_evaluate(PROFILES[0], FIXTURE_Q, tuple(bad_rows))
    assert not bad[0] and not bad[1]

    total_cases = total_nodes = total_complete = controls = 0
    for degrees, expected in zip(PROFILES, EXPECTED):
        cases = nodes = complete = 0
        controls += normalization_control(degrees)
        for shapes, q in q_options(degrees):
            count, graphs = search_case(degrees, q)
            cases += 1
            nodes += count
            complete += len(graphs)
            for rows in graphs:
                checked = literal_evaluate(degrees, q, rows)
                assert all(checked[:5]), (degrees, q, rows, checked)
                assert checked[5] is not None, (degrees, q, rows)
            if args.verbose:
                print(degrees, shapes, 'nodes=', count, 'intermediate=', len(graphs))
        assert (cases, nodes, complete) == expected
        total_cases += cases
        total_nodes += nodes
        total_complete += complete
    assert controls == 108
    assert (total_cases, total_nodes, total_complete) == (24, 5078, 135)
    print('PASS: 108 normalization controls; 24 cases; 5078 search nodes; '
          '135 intermediate graphs, all rejected by literal five-walks.')
    print(f'Elapsed: {perf_counter() - begin:.3f} seconds')


if __name__ == '__main__':
    main()

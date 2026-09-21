#!/usr/bin/env python3
"""Check all 81 full-edge-rotation K=19/20 nine-central graph cases.

Reuses the adjacent whole-orbit engine and independent literal evaluator;
no external packages, SAT solver, or magma-table enumeration are involved.
"""

import argparse
import importlib.util
import sys
from pathlib import Path
from time import perf_counter

engine_path = Path(__file__).with_name('1485_m9_sixteen_closed_orbits_check.py')
spec = importlib.util.spec_from_file_location('closed_rotation_engine', engine_path)
engine = importlib.util.module_from_spec(spec)
spec.loader.exec_module(engine)

CASES = (
    (19, 0, 14, 3302, 0),
    (19, 1, 9, 3884, 0),
    (19, 2, 10, 3959, 0),
    (20, 0, 11, 2345, 2),
    (20, 1, 10, 3360, 0),
    (20, 2, 12, 4147, 0),
    (20, 3, 15, 4081, 0),
)
FIXTURE_Q = (0, 2, 1, 4, 5, 6, 3)
FIXTURE_ROWS = (6, 41, 81, 28, 50, 100, 74)


def main():
    if sys.flags.optimize:
        raise SystemExit('Run without -O: this checker requires its assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verbose', action='store_true')
    args = parser.parse_args()
    begin = perf_counter()

    fixture = engine.literal_evaluate((2, 3, 3, 3, 3, 3, 3), FIXTURE_Q, FIXTURE_ROWS)
    assert all(fixture[:5]) and fixture[5] is not None
    damaged_rows = list(FIXTURE_ROWS)
    damaged_rows[0] ^= 2  # Delete 0→1: degrees and rotation closure must fail.
    damaged = engine.literal_evaluate((2, 3, 3, 3, 3, 3, 3), FIXTURE_Q,
                                      tuple(damaged_rows))
    assert not damaged[0] and not damaged[1]

    totals = [0, 0, 0]
    controls = 0
    intermediate = []
    for K, n4, expected_cases, expected_nodes, expected_graphs in CASES:
        n2 = 21 - K + n4
        n3 = 7 - n2 - n4
        degrees = (2,) * n2 + (3,) * n3 + (4,) * n4
        assert sum(degrees) == K and len(degrees) == 7
        controls += engine.normalization_control(degrees)
        counts = [0, 0, 0]
        for shape, q in engine.q_options(degrees):
            nodes, graphs = engine.search_case(degrees, q)
            counts[0] += 1
            counts[1] += nodes
            counts[2] += len(graphs)
            for rows in graphs:
                checked = engine.literal_evaluate(degrees, q, rows)
                assert all(checked[:5]), (degrees, q, rows, checked)
                assert checked[5] is not None, (degrees, q, rows)
                intermediate.append((K, n4, q, rows))
            if args.verbose:
                print(K, n4, shape, 'nodes=', nodes, 'intermediate=', len(graphs))
        assert tuple(counts) == (expected_cases, expected_nodes, expected_graphs)
        totals = [a + b for a, b in zip(totals, counts)]
    assert controls == 1260
    assert totals == [81, 25078, 2]
    assert (20, 0, FIXTURE_Q, FIXTURE_ROWS) in intermediate
    print('PASS: 1260 normalization controls; 81 cases; 25078 search nodes; '
          'two intermediate graphs, both rejected by literal five-walks.')
    print(f'Elapsed: {perf_counter() - begin:.3f} seconds')


if __name__ == '__main__':
    main()

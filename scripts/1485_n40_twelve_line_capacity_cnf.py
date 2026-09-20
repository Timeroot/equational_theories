#!/usr/bin/env python3
"""Necessary A12 no-high incidence and predecessor-line capacity CNFs.

Only the 4431 pattern is claimed excluded, with a separately checked LRAT
proof. The other patterns have positive necessary-incidence controls, not
magma models. Successor profiles are not assumed to use a single coset.
"""

import argparse
from itertools import combinations, product
from pathlib import Path
from runpy import run_path
from time import perf_counter


SHARED = run_path(str(Path(__file__).with_name('1485_n40_twelve_one_high_cnf.py')))
CNF = SHARED['CNF']
N = 8
SHARP = (2, 2, 2, 2, 1, 1, 1, 1)
PATTERNS = ('4431', '4422', '4332', '3333')


def build(pattern):
    assert pattern in PATTERNS
    multiplicity = tuple(map(int, pattern))
    cnf = CNF()
    D = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    C = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    colors = [[cnf.variable() for _ in range(4)] for _ in range(N)]
    # Unary M[b][p][k] means |TopPred(b) intersect P_p| >= k+1.
    M = [[[cnf.variable() for _ in range(3)] for _ in range(4)] for _ in range(N)]
    for b in range(N):
        for matrix, degree in ((D, 4 - SHARP[b]), (C, SHARP[b])):
            cnf.exact(matrix[b], degree)
            cnf.exact([matrix[a][b] for a in range(N)], degree)
        cnf.exact(colors[b], SHARP[b])
        for p in range(4):
            for k in (1, 2):
                cnf.imply([M[b][p][k]], [M[b][p][k - 1]])
        cnf.exact([M[b][p][k] for p in range(4) for k in range(3)], 4)
    for p in range(4):
        cnf.exact([colors[b][p] for b in range(N)], multiplicity[p])
        cnf.exact([M[b][p][k] for b in range(N) for k in range(3)],
                  20 - 4 * multiplicity[p])
    for a, c in product(range(N), repeat=2):
        for b, d in combinations(range(N), 2):
            cnf.imply([D[a][b], D[b][c], D[a][d], D[d][c]], [C[a][c]])
    for b, d in product(range(N), repeat=2):
        beta = [cnf.conjunction([D[d][x], C[b][x]]) for x in range(N)]
        eta = [cnf.conjunction([D[y][b], C[y][d]]) for y in range(N)]
        # Both counts are at most two, by the C row/column margins.
        ge_beta = cnf.thresholds(beta, 2)
        ge_eta = cnf.thresholds(eta, 2)
        for k in (1, 2):
            cnf.imply([D[b][d], ge_beta[k]], [ge_eta[k]])
            cnf.imply([D[b][d], ge_eta[k]], [ge_beta[k]])
        events = eta + [cnf.conjunction([colors[d][p], M[b][p][k]])
                        for p in range(4) for k in range(3)]
        ge = cnf.thresholds(events, 4)
        cnf.imply([D[b][d]], [ge[3]])
        cnf.imply([D[b][d]], [-ge[4]])
    for a, b, c, d in product(range(N), repeat=4):
        guards = [D[a][b], D[b][c], D[c][d], C[d][a]]
        cnf.imply(guards + [C[a][c]], [C[b][d]])
        cnf.imply(guards + [C[b][d]], [C[a][c]])
    return cnf, D, C, colors, M


def controls():
    SHARED['test_counter_encoding']()
    # This genuine positive necessary-incidence system passes ALL encoded
    # constraints for the 4422 pattern. It is not a magma multiplication.
    Drows = ((4, 6), (4, 5), (5, 7), (6, 7), (0, 1, 5),
             (1, 2, 4), (0, 3, 7), (2, 3, 6))
    Crows = ((0, 2), (1, 3), (0, 2), (1, 3), (4,), (5,), (6,), (7,))
    color_rows = ((0, 1), (0, 1), (0, 1), (0, 1), (2,), (3,), (3,), (2,))
    counts = ((0, 0, 2, 2),) * 4 + ((2, 0, 0, 2), (1, 1, 2, 0),
                                   (1, 1, 2, 0), (0, 2, 0, 2))
    cnf, D, C, colors, M = build('4422')
    inputs = {table[i][j]: j in rows[i]
              for table, rows in ((D, Drows), (C, Crows), (colors, color_rows))
              for i, row in enumerate(table) for j in range(len(row))}
    inputs.update({M[b][p][k]: counts[b][p] >= k + 1
                   for b in range(N) for p in range(4) for k in range(3)})
    _, truth = cnf.evaluate_extension(inputs)
    assert all(any(truth(lit) for lit in row) for row in cnf.clauses)
    # Wrong unary data must fail; auxiliary definitions are reevaluated.
    broken = dict(inputs)
    broken[M[0][0][0]] = True
    _, truth = cnf.evaluate_extension(broken)
    assert not all(any(truth(lit) for lit in row) for row in cnf.clauses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pattern', choices=PATTERNS, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf, *_ = build(args.pattern)
    with args.output.open('w') as stream:
        stream.write(f'c E1485 A12 no-high, predecessor multiplicities {args.pattern}\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter() - start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

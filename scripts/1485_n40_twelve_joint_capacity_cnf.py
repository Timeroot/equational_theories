#!/usr/bin/env python3
"""Necessary A12 both-single-coset joint profile and hole-capacity CNFs.

The six non-3333 cases require independently checked refutations before
they are exclusions. The 3333/3333 case is a positive necessary-incidence
control, not a magma. No mixed-successor-coset case is encoded here.
"""

import argparse
from itertools import combinations, permutations, product
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_n40_twelve_line_capacity_cnf.py')))
N = 8
SHARP = (2, 2, 2, 2, 1, 1, 1, 1)
PATTERNS = ('4422', '4332', '3333')


def grids(first, second):
    """Every four-hole profile-grid orbit under margin-preserving relabeling."""
    u, v = tuple(map(int, first)), tuple(map(int, second))
    rows = [p for p in permutations(range(4)) if all(u[p[i]] == u[i] for i in range(4))]
    cols = [p for p in permutations(range(4)) if all(v[p[i]] == v[i] for i in range(4))]
    seen = set()
    for holes in combinations(range(16), 4):
        if any(sum(h // 4 == p for h in holes) != 4 - u[p] for p in range(4)):
            continue
        if any(sum(h % 4 == q for h in holes) != 4 - v[q] for q in range(4)):
            continue
        if holes in seen:
            continue
        for rp, cp in product(rows, cols):
            seen.add(tuple(sorted(4 * rp[h // 4] + cp[h % 4] for h in holes)))
        yield tuple((p, q) for p, q in product(range(4), repeat=2) if 4 * p + q not in holes)


def cases():
    for i, first in enumerate(PATTERNS):
        for second in PATTERNS[i:]:
            if first == second == '3333':
                continue
            for orbit in range(len(list(grids(first, second)))):
                yield first, second, orbit


def build(first, second, orbit):
    assert first in PATTERNS and second in PATTERNS
    grid = list(grids(first, second))[orbit]
    cnf, D, C, Fcolors, M = BASE['build'](first)
    Gcolors = [[cnf.variable() for _ in range(4)] for _ in range(N)]
    Qcounts = [[[cnf.variable() for _ in range(3)] for _ in range(4)] for _ in range(N)]
    F = [[cnf.variable() for _ in range(N)] for _ in grid]
    G = [[cnf.variable() for _ in range(N)] for _ in grid]
    for b in range(N):
        cnf.exact(Gcolors[b], SHARP[b])
        cnf.exact([F[a][b] for a in range(12)], SHARP[b])
        cnf.exact([G[a][b] for a in range(12)], SHARP[b])
        for q in range(4):
            for k in (1, 2):
                cnf.imply([Qcounts[b][q][k]], [Qcounts[b][q][k - 1]])
        cnf.exact([Qcounts[b][q][k] for q in range(4) for k in range(3)], 4)
    for q in range(4):
        cnf.exact([Gcolors[b][q] for b in range(N)], int(second[q]))
        cnf.exact([Qcounts[b][q][k] for b in range(N) for k in range(3)],
                  20 - 4 * int(second[q]))
    for a in range(12):
        cnf.exact(F[a], 1)
        cnf.exact(G[a], 1)
    for b in range(N):
        for p in range(4):
            cnf.exact([-Fcolors[b][p]] +
                      [F[a][b] for a in range(12) if grid[a][0] == p], 1)
        for q in range(4):
            cnf.exact([-Gcolors[b][q]] +
                      [G[a][b] for a in range(12) if grid[a][1] == q], 1)
    for b, d in product(range(N), repeat=2):
        # C edges on both color sides must represent the same actual A vertex.
        matches = [cnf.conjunction([G[a][b], F[a][d]]) for a in range(12)]
        cnf.exact([-C[b][d]] + matches, 1)
        beta = [cnf.conjunction([C[b][x], D[d][x]]) for x in range(N)]
        events = beta + [cnf.conjunction([Gcolors[b][q], Qcounts[d][q][k]])
                         for q in range(4) for k in range(3)]
        ge = cnf.thresholds(events, 4)
        cnf.imply([D[b][d]], [ge[3]])
        cnf.imply([D[b][d]], [-ge[4]])
    # The opposite profile multiplicities force affineness of medium profiles
    # when they contain at most one four. Permitted intersections are 1111 or
    # a permutation of 2200; a whole partition line is already impossible.
    for counts, opposite in ((M, second), (Qcounts, first)):
        if opposite.count('4') >= 2:
            continue
        for b in range(4):
            for p in range(4):
                cnf.clause([-counts[b][p][2]])
                for q in range(4):
                    cnf.imply([counts[b][p][0], -counts[b][p][1]], [counts[b][q][0]])
                    cnf.imply([counts[b][p][0], -counts[b][p][1]], [-counts[b][q][1]])
    empty = [(p, q) for p, q in product(range(4), repeat=2) if (p, q) not in grid]
    for b in range(N):
        tau = [cnf.conjunction([D[v][b], D[b][d], C[v][d]])
               for v, d in product(range(N), repeat=2)]
        lower, upper = {}, {}
        for p, q in empty:
            upper[p, q] = [cnf.conjunction([M[b][p][k], Qcounts[b][q][ell]])
                           for k, ell in product(range(3), repeat=2)]
            # Deleting the three diagonal unary products subtracts min(m,n).
            lower[p, q] = [cnf.conjunction([M[b][p][k], Qcounts[b][q][ell]])
                           for k, ell in product(range(3), repeat=2) if k != ell]
        lo = tau + [event for cell in empty for event in lower[cell]]
        hi = tau + [event for cell in empty for event in upper[cell]]
        bound = 12 - 3 * SHARP[b]
        cnf.clause([cnf.at_most(lo, bound)])
        cnf.clause([cnf.thresholds(hi, bound)[bound]])
        for coordinate, counts in ((0, M[b]), (1, Qcounts[b])):
            for value in range(4):
                events = [event for cell in empty if cell[coordinate] == value
                          for event in lower[cell]]
                for amount in range(4):
                    guards = []
                    if amount > 0:
                        guards.append(counts[value][amount - 1])
                    if amount < 3:
                        guards.append(-counts[value][amount])
                    cnf.imply(guards, [cnf.at_most(events, amount * (4 - SHARP[b]))])
    return cnf, grid, D, C, F, G, Fcolors, Gcolors, M, Qcounts


def controls():
    BASE['controls']()
    assert len(list(cases())) == 6
    inventory = {(p, q): len(list(grids(p, q)))
                 for i, p in enumerate(PATTERNS) for q in PATTERNS[i:]}
    assert inventory == {('4422', '4422'): 1, ('4422', '4332'): 1,
                         ('4422', '3333'): 1, ('4332', '4332'): 2,
                         ('4332', '3333'): 1, ('3333', '3333'): 1}
    for m, n in product(range(4), repeat=2):
        upper = sum(m > k and n > ell for k, ell in product(range(3), repeat=2))
        lower = sum(m > k and n > ell for k, ell in product(range(3), repeat=2) if k != ell)
        assert upper == m * n and lower == m * n - min(m, n)
    # A substantive positive joint system: all capacities and affine-medium
    # restrictions hold, although this does NOT define a magma.
    cnf, grid, D, C, F, G, Fc, Gc, M, Qcounts = build('3333', '3333', 0)
    Drows = ((4, 5), (6, 7), (4, 7), (5, 6), (0, 3, 7),
             (0, 2, 6), (1, 2, 4), (1, 3, 5))
    Crows = ((0, 1), (0, 1), (2, 3), (2, 3), (5,), (4,), (7,), (6,))
    f = (0, 7, 1, 1, 0, 5, 2, 6, 3, 4, 3, 2)
    g = (1, 6, 0, 1, 0, 4, 2, 7, 3, 5, 2, 3)
    m = ((0, 2, 0, 2), (2, 0, 2, 0), (2, 0, 0, 2), (0, 2, 2, 0),
         (2, 0, 2, 0), (1, 1, 2, 0), (1, 1, 0, 2), (0, 2, 0, 2))
    n = ((2, 0, 0, 2), (0, 2, 2, 0), (2, 0, 2, 0), (0, 2, 0, 2),
         (1, 1, 2, 0), (0, 2, 2, 0), (2, 0, 0, 2), (1, 1, 0, 2))
    inputs = {table[b][d]: d in rows[b]
              for table, rows in ((D, Drows), (C, Crows))
              for b, d in product(range(N), repeat=2)}
    inputs.update({table[a][b]: targets[a] == b for table, targets in ((F, f), (G, g))
                   for a in range(12) for b in range(N)})
    for table, targets, coordinate in ((Fc, f, 0), (Gc, g, 1)):
        inputs.update({table[b][p]: any(targets[a] == b and grid[a][coordinate] == p
                                       for a in range(12))
                       for b in range(N) for p in range(4)})
    inputs.update({table[b][p][k]: values[b][p] >= k + 1
                   for table, values in ((M, m), (Qcounts, n))
                   for b in range(N) for p in range(4) for k in range(3)})
    _, truth = cnf.evaluate_extension(inputs)
    assert all(any(truth(lit) for lit in clause) for clause in cnf.clauses)
    broken = dict(inputs)
    broken[F[0][f[0]]] = False
    _, truth = cnf.evaluate_extension(broken)
    assert not all(any(truth(lit) for lit in clause) for clause in cnf.clauses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', choices=PATTERNS, required=True)
    parser.add_argument('--second', choices=PATTERNS, required=True)
    parser.add_argument('--orbit', type=int, default=0)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf, *_ = build(args.first, args.second, args.orbit)
    with args.output.open('w') as stream:
        stream.write(f'c E1485 A12 joint line capacities {args.first}/{args.second}, orbit {args.orbit}\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            stream.write(' '.join(map(str, clause)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter() - start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Necessary exact top-profile geometry for A12 single-coset 3333/3333.

A separate, independently verified refutation is required for exclusion.
No zero-edge elimination or conjectured full-core identity is assumed.
"""

import argparse
from itertools import product
from pathlib import Path
from runpy import run_path
from time import perf_counter


HERE = Path(__file__).parent
JOINT = run_path(str(HERE / '1485_n40_twelve_joint_capacity_cnf.py'))
GEOMETRY = run_path(str(HERE / '1485_n40_single_coset_check.py'))
GL2, OMEGAS, apply, compose = (GEOMETRY[k] for k in ('GL2', 'OMEGAS', 'apply', 'compose'))
SHARP = (2, 2, 2, 2, 1, 1, 1, 1)
GEOMETRIES = tuple(product(GL2, OMEGAS, GL2, range(4)))


def labels(geometry, point):
    L, omega, R, delta = geometry
    p, q = divmod(point, 4)
    successor = p ^ apply(R, q)
    predecessor = apply(L, p ^ apply(omega, apply(R, q))) ^ delta
    return predecessor, successor


def central_table(cnf):
    which = [cnf.variable() for _ in GEOMETRIES]
    cnf.exact(which, 1)
    central = [[cnf.disjunction([lit for lit, geometry in zip(which, GEOMETRIES)
                                 if labels(geometry, u)[1] == labels(geometry, v)[0]])
                for v in range(16)] for u in range(16)]
    return which, central


def build():
    cnf, grid, D, C, F, G, Fc, Gc, M, N = JOINT['build']('3333', '3333', 0)
    U = [[cnf.variable() for _ in range(16)] for _ in range(8)]
    V = [[cnf.variable() for _ in range(16)] for _ in range(8)]
    which, central = central_table(cnf)
    # Invertible L and translation delta do not change the predecessor fibers.
    for matrix in GL2:
        choice_c = cnf.disjunction([lit for lit, (_, _, R, _) in zip(which, GEOMETRIES)
                                    if R == matrix])
        choice_h = cnf.disjunction([lit for lit, (_, omega, R, _) in zip(which, GEOMETRIES)
                                    if compose(omega, R) == matrix])
        for b, label in product(range(8), range(4)):
            for table, guard in ((U, choice_h), (V, choice_c)):
                events = [table[b][4 * p + q] for p, q in product(range(4), repeat=2)
                          if p ^ apply(matrix, q) == label]
                ge = cnf.thresholds(events, 2)
                cnf.imply([guard], [ge[1]])
                cnf.imply([guard], [-ge[2]])
    # Existing line capacities are the intersections of actual top-point sets.
    for b, p in product(range(8), range(4)):
        for table, counts, points in ((U, M, [4 * p + q for q in range(4)]),
                                      (V, N, [4 * q + p for q in range(4)])):
            ge = cnf.thresholds([table[b][t] for t in points], 4)
            cnf.clause([-ge[4]])
            for k in range(1, 4):
                cnf.imply([ge[k]], [counts[b][p][k - 1]])
                cnf.imply([counts[b][p][k - 1]], [ge[k]])
    # A top vertex has one central, four top and three A neighbors each way.
    for t in range(16):
        cnf.exact([U[b][t] for b in range(8)], 2)
        cnf.exact([V[b][t] for b in range(8)], 2)
    for b, p in product(range(4), repeat=2):
        cnf.exact([U[b][4 * q + p] for q in range(4)], 1)
        cnf.exact([V[b][4 * p + q] for q in range(4)], 1)
    # Good top pairs are exactly the noncentral diagonal-hole pairs.
    for b in range(8):
        tau = [cnf.conjunction([D[v][b], D[b][d], C[v][d]])
               for v, d in product(range(8), repeat=2)]
        good = [cnf.conjunction([U[b][u], V[b][v], -central[u][v]])
                for u, v in product(range(16), repeat=2) if u // 4 == v % 4]
        cnf.exact(tau + good, 12 - 3 * SHARP[b])
    for u, v in product(range(16), repeat=2):
        if u // 4 != v % 4:
            continue
        middles = [cnf.conjunction([U[b][u], V[b][v]]) for b in range(8)]
        cnf.imply([-central[u][v]], [cnf.at_most(middles, 1)])
    # Without an A or B middle, a B/B pair has one ordinary top middle.
    for b, d in product(range(8), repeat=2):
        internal = cnf.disjunction([cnf.conjunction([D[b][x], D[x][d]]) for x in range(8)])
        top = [cnf.conjunction([V[b][t], U[d][t]]) for t in range(16)]
        ge = cnf.thresholds(top, 2)
        cnf.imply([-C[b][d], -internal], [ge[1]])
        cnf.imply([-C[b][d], -internal], [-ge[2]])
    # The analogous A/B and B/A conditions include all low-sharp profiles.
    for a, (p, q) in enumerate(grid):
        for b in range(8):
            first = cnf.thresholds([U[b][4 * x + q] for x in range(4)], 2)
            second = cnf.thresholds([V[b][4 * p + x] for x in range(4)], 2)
            for d in range(8):
                cnf.imply([F[a][d], -D[d][b]], [first[1]])
                cnf.imply([F[a][d], -D[d][b]], [-first[2]])
                cnf.imply([G[a][d], -D[b][d]], [second[1]])
                cnf.imply([G[a][d], -D[b][d]], [-second[2]])
    # Medium affineness and exact edge sums force beta=eta=1 on these edges.
    for b, d in product(range(8), repeat=2):
        if b >= 4 and d >= 4:
            continue
        eta = [cnf.conjunction([D[y][b], C[y][d]]) for y in range(8)]
        ge = cnf.thresholds(eta, 2)
        cnf.imply([D[b][d]], [ge[1]])
        cnf.imply([D[b][d]], [-ge[2]])
    # Exact four-element translation fibers, point by point.
    for b, t in product(range(8), range(16)):
        internal = [cnf.conjunction([D[b][d], -Fc[d][t // 4]]) for d in range(8)]
        top = [cnf.conjunction([V[b][v], -central[t][v]])
               for v in range(16) if t // 4 == v % 4]
        ge = cnf.thresholds(internal + top, 5 - SHARP[b])
        cnf.imply([U[b][t]], [ge[4 - SHARP[b]]])
        cnf.imply([U[b][t]], [-ge[5 - SHARP[b]]])
        internal = [cnf.conjunction([D[d][b], -Gc[d][t % 4]]) for d in range(8)]
        top = [cnf.conjunction([U[b][u], -central[u][t]])
               for u in range(16) if u // 4 == t % 4]
        ge = cnf.thresholds(internal + top, 5 - SHARP[b])
        cnf.imply([V[b][t]], [ge[4 - SHARP[b]]])
        cnf.imply([V[b][t]], [-ge[5 - SHARP[b]]])
    return cnf


def controls():
    JOINT['controls']()
    assert len(GEOMETRIES) == 288 and len(set(GEOMETRIES)) == 288
    # Every candidate is an actual central 4x4 grid, with both partitions
    # transversal to both actual central-label directions.
    for geometry in GEOMETRIES:
        point_labels = [labels(geometry, t) for t in range(16)]
        assert len(set(point_labels)) == 16
        for value in range(4):
            for points in ([4 * value + q for q in range(4)],
                           [4 * p + value for p in range(4)]):
                assert all(len({point_labels[t][coordinate] for t in points}) == 4
                           for coordinate in (0, 1))
    # Independently evaluate the shared central-table encoding at every one-hot
    # geometry assignment, including every auxiliary gate and every table entry.
    cnf = JOINT['BASE']['CNF']()
    which, central = central_table(cnf)
    for chosen, geometry in enumerate(GEOMETRIES):
        _, truth = cnf.evaluate_extension({lit: i == chosen for i, lit in enumerate(which)})
        assert all(any(truth(lit) for lit in clause) for clause in cnf.clauses)
        assert all(truth(central[u][v]) == (labels(geometry, u)[1] == labels(geometry, v)[0])
                   for u, v in product(range(16), repeat=2))
    # The per-top fiber count is the complete disjoint partition into j sharp
    # A inputs, good internal inputs, and good top inputs.
    for j in (1, 2):
        for neighbors in product((False, True), repeat=4 - j):
            internal = sum(not is_bad for is_bad in neighbors)
            good_top = 4 - j - internal
            assert good_top == sum(neighbors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build()
    with args.output.open('w') as stream:
        stream.write('c E1485 A12 single-coset 3333/3333 exact geometry and individual fibers\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            stream.write(' '.join(map(str, clause)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter() - start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

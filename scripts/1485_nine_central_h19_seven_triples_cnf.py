#!/usr/bin/env python3
"""Necessary incidence CNF for one r4,m9,h19 first-output case.

The central-type matrix is ((9,0,0),(0,0,3),(0,3,4)).  This script
requires a degree-five/four-top-neighbor profile.  It does not assert
UNSAT or verify a refutation.  No total-order-forty bound is encoded.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_nine_central_h18_cnf.py')))
CNF = BASE['CNF']
TYPES = [(1,1)]*9 + [(2,3)]*3 + [(3,2)]*3 + [(3,3)]*4


def profile_constraints(cnf, P, C, K):
    """Choose four source and target blocks, with a permutation K submatrix."""
    tops, central = len(P), len(P[0])
    U = [cnf.variable() for _ in range(tops)]
    V = [cnf.variable() for _ in range(tops)]
    cnf.exact(U, 4)
    cnf.exact(V, 4)
    for z in range(central):
        cnf.exact([cnf.conjunction([U[t], P[t][z]]) for t in range(tops)], 1)
        cnf.exact([cnf.conjunction([V[t], C[t][z]]) for t in range(tops)], 1)
    edges = [[cnf.conjunction([U[s], V[t], K[s][t]])
              for t in range(tops)] for s in range(tops)]
    for row in edges:
        cnf.clause([cnf.at_most(row, 1)])
    for t in range(tops):
        cnf.clause([cnf.at_most([edges[s][t] for s in range(tops)], 1)])
    cnf.exact([e for row in edges for e in row], 4)
    return U, V


def build():
    cnf = CNF()
    P = [[cnf.variable() for _ in range(9)] for _ in TYPES]
    C = [[cnf.variable() for _ in range(9)] for _ in TYPES]
    K = BASE['central_constraints'](cnf, P, C, TYPES, 4)
    # All nine singleton/singleton tops have distinct P labels. Their
    # names can be assigned after the grid coordinates below are chosen.
    for t in range(9):
        for z in range(9):
            cnf.clause([P[t][z] if z == t else -P[t][z]])
    # The three (3,2) P-blocks partition Z; dually the three (2,3)
    # C-blocks partition Z. Orthogonality makes a full 3-by-3 grid.
    for i, t in enumerate(range(12, 15)):
        for z in range(9):
            cnf.clause([P[t][z] if z//3 == i else -P[t][z]])
    for j, t in enumerate(range(9, 12)):
        for z in range(9):
            cnf.clause([C[t][z] if z%3 == j else -C[t][z]])
    profile_constraints(cnf, P, C, K)
    return cnf


def controls():
    BASE['controls']()
    # Positive/negative tests for the profile gadget itself. These are
    # not claimed to satisfy the separate h19 central-incidence formula.
    for mutate in (False, True):
        cnf = CNF()
        blocks = [[1 if i == z else -1 for z in range(4)] for i in range(4)]
        K = [[1 if i == j else -1 for j in range(4)] for i in range(4)]
        if mutate:
            K[0][1] = 1
        U, V = profile_constraints(cnf, blocks, blocks, K)
        _, truth = cnf.evaluate_extension({v: True for v in U+V})
        satisfied = all(any(truth(v) for v in row) for row in cnf.clauses)
        assert satisfied != mutate


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: encoding controls are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build()
    with args.output.open('w') as stream:
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter()-start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

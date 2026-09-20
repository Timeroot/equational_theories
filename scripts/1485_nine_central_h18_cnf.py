#!/usr/bin/env python3
"""Necessary central-incidence CNFs for the remaining five h18 profiles.

Mathematics and complete normalization:
docs/1485_nine_central_eighteen_top.md.
This generator does not claim UNSAT or verify a solver refutation.
Default constraints are order independent; --order-forty adds a fiber bound.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_n40_twelve_one_high_cnf.py')))
CNF = BASE['CNF']
CASES = ('A010', 'A110', 'A111', 'B110', 'B111')


def normalized_profile(case):
    family, uc, vc, overlap = case[0], *map(int, case[1:])
    if family == 'A':
        types = [(1,1)]*6 + [(2,2)]*3 + [(2,3)]*3 + [(3,2)]*3 + [(3,3)]*3
    else:
        assert family == 'B'
        types = [(1,1)]*5 + [(1,2)] + [(2,1)] + [(2,2)]*3 + [(2,3)]*2 + [(3,2)]*2 + [(3,3)]*4
    both = [t for t, pair in enumerate(types) if pair == (3,3)]
    ps = [t for t, pair in enumerate(types) if pair == (3,2)]
    cs = [t for t, pair in enumerate(types) if pair == (2,3)]
    U = ps[:3-uc] + both[:uc]
    V = cs[:3-vc] + both[:overlap] + both[uc:uc+vc-overlap]
    assert len(U) == len(V) == 3 and len(set(U) & set(V)) == overlap
    return types, U, V


def central_constraints(cnf, P, C, types, valency):
    """Exact central incidence, usable separately for positive controls."""
    tops, central = len(types), len(P[0])
    for t, (p,c) in enumerate(types):
        cnf.exact(P[t], p)
        cnf.exact(C[t], c)
    for z in range(central):
        cnf.exact([P[t][z] for t in range(tops)], valency)
        cnf.exact([C[t][z] for t in range(tops)], valency)
        for w in range(central):
            cnf.exact([cnf.conjunction([P[t][z], C[t][w]])
                       for t in range(tops)], 1)
    K = []
    for s in range(tops):
        row = []
        for t in range(tops):
            events = [cnf.conjunction([C[s][z], P[t][z]]) for z in range(central)]
            cnf.clause([cnf.at_most(events, 1)])
            row.append(cnf.disjunction(events))
        K.append(row)
    return K


def complement_tilings(cnf, blocks, sizes, coordinate, order_forty):
    small = [t for t, size in enumerate(sizes) if size < 3]
    assignment = {t:[cnf.variable() for _ in range(3)] for t in small}
    for t in small:
        cnf.exact(assignment[t], 1)
    for j in range(3):
        for z in range(9):
            events = [cnf.conjunction([assignment[t][j], blocks[t][z]]) for t in small]
            cnf.exact(events, int(coordinate(z) != j))
        if order_forty:
            cnf.clause([cnf.at_most([assignment[t][j] for t in small], 5)])


def build(case, order_forty=False):
    assert case in CASES
    types, U, V = normalized_profile(case)
    cnf = CNF()
    P = [[(1 if z//3 == U.index(t) else -1) if t in U else cnf.variable()
          for z in range(9)] for t in range(18)]
    C = [[(1 if z%3 == V.index(t) else -1) if t in V else cnf.variable()
          for z in range(9)] for t in range(18)]
    K = central_constraints(cnf, P, C, types, 4)
    for z in range(9):
        cnf.exact([P[t][z] for t in range(18) if types[t][0] == 3], 2)
        cnf.exact([C[t][z] for t in range(18) if types[t][1] == 3], 2)
    for u in U:
        cnf.exact([K[u][v] for v in V], 1)
    for v in V:
        cnf.exact([K[u][v] for u in U], 1)
    complement_tilings(cnf, P, [p for p,c in types], lambda z:z%3, order_forty)
    complement_tilings(cnf, C, [c for p,c in types], lambda z:z//3, order_forty)
    return cnf


def controls():
    BASE['test_counter_encoding']()
    # Genuine 2x2 central groupoid incidence: four tops, four central labels.
    rows = [(set((2*i,2*i+1)), set((j,j+2))) for i in range(2) for j in range(2)]
    # Also check the 15-top abstract r4,m9 seed from the mathematical note.
    seed = []
    for i in range(3):
        row = {3*i+j for j in range(3)}
        for j in range(3):
            col = {3*k+j for k in range(3)}
            if i == j:
                seed.extend([(row,{3*i+i}), (row,col-{3*i+i})])
            elif j == (i+1)%3:
                seed.extend([({3*i+i},col), (row-{3*i+i},col)])
            else:
                seed.append((row,col))
    for central, valency, fixture in ((4,2,rows),(9,4,seed)):
        cnf = CNF()
        types = [(len(p),len(c)) for p,c in fixture]
        P = [[cnf.variable() for _ in range(central)] for _ in fixture]
        C = [[cnf.variable() for _ in range(central)] for _ in fixture]
        central_constraints(cnf, P, C, types, valency)
        inputs = {matrix[t][z]: z in fixture[t][side]
                  for side,matrix in enumerate((P,C))
                  for t in range(len(fixture)) for z in range(central)}
        _, truth = cnf.evaluate_extension(inputs)
        assert all(any(truth(lit) for lit in clause) for clause in cnf.clauses)
        # Removing one incidence destroys the prescribed block cardinality.
        changed = dict(inputs)
        positive = next(variable for variable, value in inputs.items() if value)
        changed[positive] = False
        _, truth = cnf.evaluate_extension(changed)
        assert not all(any(truth(lit) for lit in clause) for clause in cnf.clauses)
    # These positive controls test the central encoding only. The 15-top
    # fixture is deliberately NOT claimed to satisfy the h18 refinements.


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: encoding controls are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, required=True)
    parser.add_argument('--order-forty', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build(args.case, args.order_forty)
    with args.output.open('w') as stream:
        stream.write(f'c E1485 r4 m9 h18 case {args.case}; order40={args.order_forty}\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str,row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter()-start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Final balanced A12 line-capacity CNF, without global affine coordinates.

Adds analytic all-weight-one and no-three-point-line theorems, then the
regular-hole matching condition. Independently check the resulting LRAT
proof; a diagnostic solver verdict alone is not a certificate.
"""

import argparse
from itertools import product
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_n40_twelve_joint_capacity_cnf.py')))
CNF = BASE['BASE']['CNF']


def regular_hole(cnf, first, second, outgoing, incoming):
    """Exact necessary counts for an empty or perfect central matching.

    first/second are the three unary bits of m,n (already at most2).
    outgoing/incoming list the Boolean events counting the two good degrees.
    """
    eg, fg = cnf.thresholds(outgoing, 4), cnf.thresholds(incoming, 4)

    def equal(ge, amount):
        return cnf.conjunction([ge[amount], -ge[amount + 1]])

    for m, n in product(range(3), repeat=2):
        guards = []
        for counts, value in ((first, m), (second, n)):
            if value:
                guards.append(counts[value - 1])
            guards.append(-counts[value])
        if m == n == 0:
            continue
        if m == 0:
            cnf.imply(guards, [-fg[1]])
        elif n == 0:
            cnf.imply(guards, [-eg[1]])
        else:
            choices = [cnf.conjunction([equal(eg, n), equal(fg, m)])]
            if m == n:
                choices.append(cnf.conjunction([equal(eg, n - 1), equal(fg, m - 1)]))
            cnf.imply(guards, choices)


def build():
    cnf, grid, D, C, F, G, Fc, Gc, M, N = BASE['build']('3333', '3333', 0)
    assert set(grid) == {(p, q) for p in range(4) for q in range(4) if p != q}
    for b in range(8):
        for p in range(4):
            cnf.clause([-M[b][p][2]])
            cnf.clause([-N[b][p][2]])
        for d in range(8):
            beta = [cnf.conjunction([C[b][x], D[d][x]]) for x in range(8)]
            ge = cnf.thresholds(beta, 2)
            cnf.imply([D[b][d]], [ge[1]])
            cnf.imply([D[b][d]], [-ge[2]])
    for b in range(8):
        for p in range(4):
            outgoing = [cnf.conjunction([D[b][d], Fc[d][p]]) for d in range(8)]
            incoming = [cnf.conjunction([D[c][b], Gc[c][p]]) for c in range(8)]
            regular_hole(cnf, M[b][p], N[b][p], outgoing, incoming)
    return cnf


def controls():
    BASE['controls']()
    cnf = CNF()
    first, second, outgoing, incoming = [[cnf.variable() for _ in range(3)] for _ in range(4)]
    regular_hole(cnf, first, second, outgoing, incoming)
    # Exhaust all144 possible integer quadruples, including absent endpoints.
    for m, n, e, f in product(range(3), range(3), range(4), range(4)):
        inputs = {variable: value >= k + 1
                  for bits, value in ((first, m), (second, n), (outgoing, e), (incoming, f))
                  for k, variable in enumerate(bits)}
        _, truth = cnf.evaluate_extension(inputs)
        actual = all(any(truth(lit) for lit in row) for row in cnf.clauses)
        if m == n == 0:
            expected = True
        elif m == 0:
            expected = f == 0
        elif n == 0:
            expected = e == 0
        else:
            expected = (e == n and f == m) or (m == n and e == f == m - 1)
        assert actual == expected, (m, n, e, f)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build()
    with args.output.open('w') as stream:
        stream.write('c E1485 A12 balanced3333, exact regular-hole fibers\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter() - start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Necessary A12 mixed-coset10+2 incidence CNFs for4332 and4422.

The reduction is §10 of docs/1485_order_forty_twelve_no_high_profiles.md.
These formulas require one minority predecessor row of multiplicity2,
normalized to row3, and all other rows in the majority successor coset.
"""

import argparse
from itertools import product
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_n40_twelve_line_capacity_cnf.py')))


def build(pattern):
    assert pattern in ('4332', '4422')
    cnf, D, C, colors, M = BASE['build'](pattern)
    for b in range(4):
        ge = cnf.thresholds([M[b][p][1] for p in range(4)], 2)
        # Row sum4/cap3 gives three alternatives:
        # zero entries>=2:1111; one:2110/3100; two:2200.
        nonaffine = cnf.conjunction([ge[1], -ge[2]])
        rank_one = ge[2]
        for v in range(8):
            if v >= 4:
                cnf.imply([nonaffine, D[v][b]], [-1])
            # A rank-one affine profile fails minority transversality.
            # Its two predecessors are the two minority F-images.
            cnf.imply([rank_one, D[v][b]], [colors[v][3]])
        # The four exceptions of a non-affine profile fill exactly
        # its two medium predecessor F-fibers, with u_p-2 in row p.
        for p, count in enumerate(int(c) - 2 for c in pattern):
            events = [cnf.conjunction([D[v][b], colors[v][p]])
                      for v in range(4)]
            count_ge = cnf.thresholds(events, count + 1)
            if count:
                cnf.imply([nonaffine], [count_ge[count]])
            cnf.imply([nonaffine], [-count_ge[count + 1]])
    return cnf


def controls():
    BASE['controls']()
    # Check every possible unary row, including the distinction between
    # the two new guarded branches and the unrestricted1111 branch.
    for counts in product(range(4), repeat=4):
        if sum(counts) != 4:
            continue
        cnf = BASE['CNF']()
        inputs = [cnf.variable() for _ in range(4)]
        ge = cnf.thresholds(inputs, 2)
        nonaffine = cnf.conjunction([ge[1], -ge[2]])
        _, truth = cnf.evaluate_extension(dict(zip(inputs, (v >= 2 for v in counts))))
        assert truth(nonaffine) == (sorted(counts) in ([0, 0, 1, 3], [0, 1, 1, 2]))
        assert truth(ge[2]) == (sorted(counts) == [0, 0, 2, 2])
        assert (not truth(ge[1])) == (counts == (1, 1, 1, 1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pattern', choices=('4332', '4422'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build(args.pattern)
    with args.output.open('w') as stream:
        stream.write(f'c E1485 A12 mixed10+2, predecessor multiplicities {args.pattern}\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter()-start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

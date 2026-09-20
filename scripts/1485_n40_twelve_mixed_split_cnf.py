#!/usr/bin/env python3
"""Certify the balanced mixed-coset affine/non-affine split cases.

The analytic reduction is §9 of
docs/1485_order_forty_twelve_no_high_profiles.md. This encoding does not
apply to exceptional 4332 or4422 arrangements with successor populations10+2.
"""

import argparse
from itertools import product
from pathlib import Path
from runpy import run_path
from time import perf_counter


BASE = run_path(str(Path(__file__).with_name('1485_n40_twelve_line_capacity_cnf.py')))


def build(pattern):
    assert pattern in ('3333', '4332', '4422')
    cnf, D, C, colors, M = BASE['build'](pattern)
    # Relabel the four medium vertices: 0,1 are the two central-column
    # profiles; 2,3 are the two non-affine profiles. All have sharp degree2.
    for a in (0, 1):
        for p in range(4):
            cnf.clause([M[a][p][0]])
            cnf.clause([-M[a][p][1]])
        for low in range(4, 8):
            cnf.clause([-D[a][low]])
    for n in (2, 3):
        # With sum4 and entries0..3, exactly one entry>=2 means that
        # the multiset of entries is2110 or3100, precisely the required
        # non-affine P-margin shapes. No affine coordinates are encoded.
        cnf.exact([M[n][p][1] for p in range(4)], 1)
        for low in range(4, 8):
            cnf.clause([-D[low][n]])
    return cnf


def controls():
    BASE['controls']()
    for counts in product(range(4), repeat=4):
        if sum(counts) == 4:
            assert (sum(value >= 2 for value in counts) == 1) == (
                sorted(counts) in ([0, 0, 1, 3], [0, 1, 1, 2]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pattern', choices=('3333', '4332', '4422'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    controls()
    cnf = build(args.pattern)
    with args.output.open('w') as stream:
        stream.write(f'c E1485 A12 mixed split, predecessor multiplicities {args.pattern}\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for row in cnf.clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; '
          f'{perf_counter()-start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()

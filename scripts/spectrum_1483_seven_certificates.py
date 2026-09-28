#!/usr/bin/env python3
"""Reproduce and audit the nine small LRAT checks excluding E1483 at seven."""
import argparse
import inspect
import itertools
import json
from pathlib import Path

import definability_1483_sat_check as old
from spectrum_1483_ten_certificates import render as render_ten, verify

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data/spectrum/1483_order7_refutation.json'
DEST = ROOT / 'equational_theories/Spectrum/Equation1483/SevenCases'
CASES = [(2, False)] + [(k, z) for k in range(3, 7) for z in (False, True)]


def cnf_bytes(k, zero):
    source = inspect.getsource(old.cnf_clauses)
    source = source.replace('assert (k, zero) in CASES', 'assert (k, zero) in allowed')
    source = source.replace('n = 11', 'n = 7')
    start = source.index('    # Rows of rank three')
    end = source.index('    for y in range(k + 1', start)
    source = source[:start] + source[end:]
    start = source.index('    # Semantically necessary')
    end = source.index('    clauses = [cl', start)
    source = source[:start] + source[end:]
    env = {'itertools': itertools, 'allowed': CASES}
    exec(source, env)
    cs = env['cnf_clauses'](k, zero)
    return (f'p cnf 3773 {len(cs)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs)).encode()


def render(d):
    return (render_ten(d).replace('TenSAT', 'SevenSAT').replace('OrderTen', 'OrderSeven')
            .replace('natRankFormula 10 ', 'natRankFormula 7 '))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write', action='store_true')
    p.add_argument('--export-cnf', type=Path)
    args = p.parse_args()
    cases = json.loads(DATA.read_text())['cases']
    assert sorted((d['rank'], d['zero_in_image']) for d in cases) == CASES
    for d in cases:
        path = DEST / f'Rank{d["rank"]}Zero{int(d["zero_in_image"])}.lean'
        text = render(d)
        if args.write:
            path.write_text(text)
        else:
            assert path.read_text() == text, f'{path} is stale'
        verify(d, args.export_cnf, cnf_bytes, 3773)
    print('Verified nine complete cases, source reproduction, CNFs and certificate hashes.')


if __name__ == '__main__':
    main()

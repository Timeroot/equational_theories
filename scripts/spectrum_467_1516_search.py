#!/usr/bin/env python3
"""Bounded E467/E1516 spectrum searches using squared left translations.

Both finite varieties have bijective rows, columns and squaring. Write
Q(x,y)=x*(x*y). E467 is Q(x,D(y))=L_y^{-1}(x), whereas E1516 is
Q(x,y)=L_{D(y)}^{-1}(x). Thus Q is also a Latin square. For E467 its
diagonal is D^{-1}. These consequences substantially strengthen propagation.

Research only: UNSAT is not a Lean theorem, and TIMEOUT excludes nothing.
Every SAT table is checked against the original equation independently.
No potentially enormous proof trace is produced by this script.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

from spectrum_generate import load_equations, satisfies


def clauses(law, n, normalize=True, strength=3):
    assert law in (467, 1516)
    r = range(n)
    p = lambda x, y, z: 1 + (x*n+y)*n+z
    q = lambda x, y, z: 1 + n**3 + (x*n+y)*n+z
    cs = []

    def one(v):
        cs.append(v)
        cs.extend([-a, -b] for a, b in itertools.combinations(v, 2))

    def triangle(a, b, c):
        cs.extend(([-a, -b, c], [-a, b, -c], [a, -b, -c]))

    for f in (p, q):
        for x, y in itertools.product(r, repeat=2):
            one([f(x, y, z) for z in r])
            one([f(x, z, y) for z in r])
            one([f(z, x, y) for z in r])
    for z in r:
        one([p(x, x, z) for x in r])
    for x, y, a, b in itertools.product(r, repeat=4):
        triangle(p(x, y, a), p(x, a, b), q(x, y, b))
        if law == 467:
            triangle(p(y, y, a), q(x, a, b), p(y, b, x))
        else:
            triangle(p(y, y, a), q(x, y, b), p(a, b, x))
    if law == 467:
        for x, y in itertools.product(r, repeat=2):
            cs.extend(([-p(x, x, y), q(y, y, x)],
                       [p(x, x, y), -q(y, y, x)]))
            if strength >= 1:
                # L_x and L_x² have the same unique fixed point, D²(x).
                cs.append([p(x, y, y), -q(x, y, y)])
        if strength >= 1:
            for x in r:
                one([p(x, y, y) for y in r])
                one([q(x, y, y) for y in r])
        if strength >= 2:
            for x, a, b in itertools.product(r, repeat=3):
                triangle(p(x, x, a), p(a, a, b), p(x, b, b))
                if strength >= 3 and x != a:
                    # D²x=x or D³x=x forces Dx=x.
                    cs.append([-p(x, x, a), -p(a, a, x)])
                    cs.append([-p(x, x, a), -p(a, a, b), -p(b, b, x)])
    if normalize:
        # Choose a non-idempotent 0 if possible, then label the cycles of L_0.
        cs.extend([-p(0, 0, 0), p(x, x, x)] for x in r)
        cs.extend([-p(0, y, z)] for y, z in itertools.product(r, repeat=2)
                  if z > y+1)
    return [c for c in cs if not any(-v in c for v in c)]


def order16_cycle_types():
    """Complete mathematical split using Equation467Translations.lean."""
    def parts(n, lower=3):
        if n == 0:
            yield ()
        for k in range(lower, n+1):
            for rest in parts(n-k, k):
                yield (k,)+rest
    return [(1,)+p for p in parts(15)] + [(4, 1)+p for p in parts(11)]


def first_use_clauses(n, lengths):
    """Normalize under a subgroup of the first-row centralizer fixing 1.

The initial block of columns is fixed pointwise. Rotate each remaining cycle,
and permute equal-length cycles, in the order its values first occur in row 1
at these fixed columns. This relabelling preserves the prescribed first row.
"""
    if lengths[0] == 1 and len(lengths) > 1:
        fixed = 1+lengths[1]
    elif tuple(lengths[:2]) == (4, 1):
        fixed = 5
    else:
        raise ValueError('unsupported first-row shape for first-use normalization')
    if list(lengths[2:]) != sorted(lengths[2:]):
        raise ValueError('remaining cycle lengths must be sorted')
    groups, offset, i = [], fixed, 2
    while i < len(lengths):
        length = lengths[i]
        count = lengths[i:].count(length)
        end = offset+count*length
        groups.extend((offset+j*length, end) for j in range(count))
        offset, i = end, i+count
    p = lambda x, y, z: 1+(x*n+y)*n+z
    cs = []
    for col in range(fixed):
        for start, end in groups:
            seen = [p(1,j,v) for j in range(col) for v in range(start,end)]
            cs.extend([-p(1,col,v)]+seen for v in range(start+1,end))
    return cs


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('law', type=int, choices=(467, 1516))
    ap.add_argument('order', type=int)
    ap.add_argument('--seconds', type=int, default=300)
    ap.add_argument('--idempotent', action='store_true')
    ap.add_argument('--cycles', help='cycle lengths of the first row, zero first')
    ap.add_argument('--first-use', action='store_true', help='normalize further under the first-row centralizer')
    ap.add_argument('--strength', type=int, choices=range(4), default=3,
                    help='0: Latin and square inverse; 1: fixed points; 2: D² fixed point; 3: square periods')
    ap.add_argument('--five-submodel', type=int, choices=(0, 1),
                    help='require one of the two saved non-idempotent E467 models on labels 0,...,4')
    ap.add_argument('--output', type=Path, default=Path('.cache/e467-spectrum'))
    args = ap.parse_args()
    n = args.order
    if n < 1 or args.seconds < 1:
        ap.error('order and timeout must be positive')
    if args.first_use and not args.cycles:
        ap.error('--first-use requires --cycles')
    if args.five_submodel is not None and (args.law != 467 or n < 5):
        ap.error('--five-submodel requires E467 and order at least five')
    cs = clauses(args.law, n, strength=args.strength)
    p = lambda x, y, z: 1+(x*n+y)*n+z
    tag = f'{args.law}-{n}'
    if args.idempotent:
        cs.extend([[p(x, x, x)] for x in range(n)])
        tag += '-idem'
    if args.five_submodel is not None:
        data = Path(__file__).resolve().parent.parent / 'data/spectrum/467_1516_order16_research.json'
        table = json.loads(data.read_text())['normalized_non_idempotent_five_element_tables'][args.five_submodel]
        assert satisfies(*load_equations()[466], table, 5)
        cs.extend([[p(x, y, table[5*x+y])] for x in range(5) for y in range(5)])
        tag += f'-five-submodel-{args.five_submodel}'
    if args.cycles:
        lengths = list(map(int, args.cycles.split(',')))
        if min(lengths) < 1 or sum(lengths) != n:
            ap.error('cycle lengths must be positive and sum to the order')
        row, offset = [], 0
        for length in lengths:
            row += list(range(offset+1, offset+length)) + [offset]
            offset += length
        cs.extend([[p(0, y, z)] for y, z in enumerate(row)])
        tag += '-cycles-' + args.cycles.replace(',', '_')
        if args.first_use:
            cs.extend(first_use_clauses(n, lengths))
            tag += '-first-use'
    args.output.mkdir(parents=True, exist_ok=True)
    cnf = args.output / (tag+'.cnf')
    cnf.write_text(f'p cnf {2*n**3} {len(cs)}\n' + ''.join(
        ' '.join(map(str, c))+' 0\n' for c in cs))
    start = time.monotonic()
    log = args.output / (tag+'.log')
    with log.open('w') as out:
        proc = subprocess.run(['cadical', '-t', str(args.seconds), str(cnf)],
                              stdout=out, stderr=subprocess.STDOUT)
    report = dict(law=args.law, order=n, seconds=time.monotonic()-start,
                  solver='CaDiCaL', idempotent_only=args.idempotent,
                  first_row_cycles=args.cycles, lean_checked=False,
                  first_use=args.first_use, strength=args.strength,
                  five_submodel=args.five_submodel,
                  status={0:'TIMEOUT',10:'SAT',20:'UNSAT'}.get(proc.returncode, 'UNKNOWN'),
                  exit_code=proc.returncode, time_limit=args.seconds,
                  variables=2*n**3, clauses=len(cs),
                  cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest())
    if proc.returncode == 10:
        positive = {int(v) for line in log.read_text().splitlines()
                    if line.startswith('v ') for v in line[2:].split() if int(v)>0}
        table = [next(z for z in range(n) if p(x,y,z) in positive)
                 for x,y in itertools.product(range(n), repeat=2)]
        assert satisfies(*load_equations()[args.law-1], table, n)
        report['table'] = table
    (args.output/(tag+'.json')).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()

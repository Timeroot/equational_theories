#!/usr/bin/env python3
"""Explicit PBD tail certificates for E1076 and E1313.

All records describe positive constructions. The checker independently validates
roots, products, transversal-design parameters, sum decompositions, and interval
coverage. Lean generation/checking is separate; Python verification is not a Lean
proof. See docs/quartic_cofinite_20260928.md.
"""
from bisect import bisect_right
from functools import cache
from math import isqrt
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'data/spectrum/quartic_tail_certificate.json'
CUTOFF = 107773
BASE_END = 10100000
LEVELS = [*range(500, 3001, 50), 4000, 5000, 6000, 8000, 10000, 12000]


@cache
def factors(n):
    out = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def prime(n):
    return n >= 2 and factors(n) == ((n, 1),)


@cache
def root(n):
    return next((b for b in range(n) if ((((b-1)*b-1)*b+1)*b-1) % n == 0), None)


def td(k, q):
    return q > 1 and all(p**e + 1 >= k for p, e in factors(q))


def closure(bound=30000):
    rec = {0: ['empty'], 1: ['one']}
    for n in range(2, isqrt(isqrt(bound))+1):
        rec[n**4] = ['quartic', n]
    for p in range(5, 2000):
        if prime(p) and (b := root(p)) is not None:
            rec[p] = ['scalar', b]
    # These are the field seeds used in the discovery calculation.
    rec[25] = ['product', 5, 5]
    for iteration in range(20):
        before = len(rec)
        snap = sorted(rec)
        for a in snap:
            if a*a > bound:
                break
            if a < 2:
                continue
            for b in snap:
                n = a*b
                if n > bound:
                    break
                if b >= a:
                    rec.setdefault(n, ['product', a, b])
        snap = sorted(rec)
        for q in range(16, bound//16+1):
            if not td(17, q):
                continue
            for e in (0, 1):
                if q+e not in rec:
                    continue
                for t in snap:
                    r = t-e
                    n = 16*q+r+e
                    if r > q or n > bound:
                        break
                    if r >= 0:
                        rec.setdefault(n, ['one_hole', q, r, e])
        snap = sorted(rec)
        for q in range(80, bound//79+1):
            if not td(81, q):
                continue
            for e in (0, 1):
                if q+e not in rec:
                    continue
                ss = [n-e for n in snap[:bisect_right(snap, q+e)] if n >= e]
                bits = sum(1 << n for n in ss)
                sums = 0
                for a in ss:
                    sums |= bits << a
                while sums:
                    total = (sums & -sums).bit_length()-1
                    sums &= sums-1
                    n = 79*q+total+e
                    if n > bound:
                        break
                    if n not in rec:
                        a = next(a for a in ss if total-a+e in rec and 0 <= total-a <= q)
                        rec[n] = ['two_holes', q, a, total-a, e]
        if len(rec) == before:
            return rec
    raise RuntimeError('Closure failed to stabilize')


def generate():
    rec = closure()
    sums = {}
    ranges = {}
    for B in LEVELS:
        T = sorted(n for n in rec if n <= B)
        bits = sum(1 << x for x in T)
        su = 0
        for x in T:
            su |= bits << x
        hi = 254
        while (su >> hi) & 1:
            hi += 1
        if hi > 254:
            ranges[B] = hi-1
    # Choose the furthest-reaching available interval at each step. Above
    # 12000, field seeds alone suffice for group fillings, keeping the finite
    # construction certificate small.
    chain = []
    at = CUTOFF
    while at <= BASE_END:
        found = None
        for q in range((at-254)//79, 499, -1):
            if not td(81, q):
                continue
            B = max(b for b in ranges if b <= q)
            lo, hi = 79*q+254, 79*q+ranges[B]
            if hi < at:
                break
            if prime(q) and (b := root(q)) is not None:
                rec[q] = ['scalar', b]
            elif q >= 12000 or q not in rec:
                continue
            found = [q, B, lo, hi]
            break
        if found is None:
            raise RuntimeError(f'Uncovered order {at}')
        chain.append(found)
        at = found[3]+1
    used_levels = sorted({row[1] for row in chain})
    need = {16, 17, 79, 80, 81, *[row[0] for row in chain]}
    previous = 253
    split_blocks = []
    for B in used_levels:
        hi = ranges[B]
        rs = []
        for t in range(previous+1, hi+1):
            r = next(r for r in range(t//2, -1, -1) if r in rec and t-r in rec and t-r <= B)
            rs.append(r)
            need.update((r, t-r))
        split_blocks.append({'bound': B, 'lo': previous+1, 'hi': hi, 'left': rs})
        previous = hi
    reduced = {}
    def visit(n):
        if n in reduced:
            return
        r = rec[n]
        tag = r[0]
        if tag == 'product':
            deps = r[1:]
        elif tag == 'one_hole':
            q, s, e = r[1:]
            deps = [q+e, s+e, 16, 17]
        elif tag == 'two_holes':
            q, a, b, e = r[1:]
            deps = [q+e, a+e, b+e, 79, 80, 81]
        else:
            deps = []
        assert all(d < n for d in deps), (n, r)
        for d in deps:
            visit(d)
        reduced[n] = r
    for n in sorted(need):
        visit(n)
    out = {'status': 'POSITIVE_CONSTRUCTION_CERTIFICATE',
           'lean_theorem': 'Spectrum.QuarticTail.models',
           'laws': [1076, 1313], 'cutoff': CUTOFF, 'base_end': BASE_END,
           'models': {str(n): reduced[n] for n in sorted(reduced)},
           'splits': split_blocks, 'intervals': chain}
    check(out)
    OUTPUT.write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print(f'{len(reduced)} models, {sum(len(b["left"]) for b in split_blocks)} sum splits, '
          f'{len(chain)} intervals; all orders ≥ {CUTOFF}')
    return out


def check(cert):
    done = set()
    for ns, r in sorted(cert['models'].items(), key=lambda item: int(item[0])):
        n, tag = int(ns), r[0]
        if tag == 'empty':
            assert n == 0
        elif tag == 'one':
            assert n == 1
        elif tag == 'scalar':
            b = r[1]
            assert n > 0 and (b**4-b**3-b*b+b-1) % n == 0
        elif tag == 'quartic':
            assert n == r[1]**4
        elif tag == 'product':
            a, b = r[1:]
            assert a in done and b in done and n == a*b
        elif tag in ('one_hole', 'two_holes'):
            q, *sizes, e = r[1:]
            k = 16 if tag == 'one_hole' else 79
            assert len(sizes) == (1 if k == 16 else 2)
            assert td(k+len(sizes), q) and e in (0, 1)
            assert q+e in done and all(t+e in done and 0 <= t <= q for t in sizes)
            assert all(t in done for t in range(k, k+len(sizes)+1))
            assert n == k*q+sum(sizes)+e
        else:
            raise ValueError(tag)
        done.add(n)
    prev, last_bound = 253, 0
    ranges = {}
    for block in cert['splits']:
        lo, hi, B = block['lo'], block['hi'], block['bound']
        assert lo == prev+1 and B >= last_bound and len(block['left']) == hi-lo+1
        for t, a in enumerate(block['left'], lo):
            assert a in done and t-a in done and 0 <= a <= B and 0 <= t-a <= B
        ranges[B] = hi
        prev, last_bound = hi, B
    end = cert['cutoff']-1
    for q, B, lo, hi in cert['intervals']:
        assert td(81, q) and q in done and B <= q and B in ranges
        assert lo == 79*q+254 and hi == 79*q+ranges[B]
        assert lo <= end+1 <= hi
        end = hi
    assert end >= cert['base_end']
    # For n above the checked range take q=30030*(n//510510+1)+1,
    # r=n-16q. Both are ≥ cutoff, are < n, and r≤q. Also gcd(q,30030)=1.
    # The bound below suffices for those inequalities; they are proved in the note.
    assert cert['base_end'] >= 17*cert['cutoff']+272*30031
    print('Certificate checked: roots, designs, closure, splits, coverage, induction threshold.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    args = parser.parse_args()
    if args.generate:
        generate()
    else:
        check(json.loads(OUTPUT.read_text()))

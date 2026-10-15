#!/usr/bin/env python3
"""Bounded positive-model searches; restricted UNSAT results are not exclusions.

Uses proved chain-law cancellation, or the E1483 row-image reduction. The
latter extends the independently checked order-eleven input to order twelve;
all rank-product thresholds used here remain valid at both sizes. No solver
proof is recorded. Every SAT table is checked against the original law.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

from spectrum_small_orders import clauses as chain_clauses, variables
from spectrum_generate import load_equations, satisfies

def central_base(n, k, zero):
    """Independent DIMACS encoding; clause order is part of the certificate."""
    assert n in (11, 12) and 2 <= k < n and (not zero or k >= 4)
    R = range(n)
    base = []
    a = lambda t, x, y, z: 1 + ((t * n + x) * n + y) * n + z
    p = lambda x, y, z: a(0, x, y, z)
    r = lambda x, z: a(1, x, z, 0)
    g = lambda x, y, z: a(2, x, y, z)
    c = lambda x, z: a(3, x, z, 0)
    d = lambda x, y, z: a(4, x, y, z)
    R = range(n)
    for x, y in itertools.product(R, repeat=2):
        base.append([p(x, y, z) for z in R])
    for x, y, z, w in itertools.product(R, repeat=4):
        if z != w:
            base.append([-p(x, y, z), -p(x, y, w)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(y, z, b), r(y, b)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(z, y, b), c(y, b)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(y, x, u), -r(y, b), g(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-g(x, u, b), -p(x, b, v), p(u, v, x)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(x, y, u), -c(y, b), d(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-d(x, u, b), -p(b, x, v), p(v, u, x)])

    large = lambda x: a(5, x, 0, 0)
    # Reverse implications make row/column membership exact.
    for y, b in itertools.product(R, repeat=2):
        base.append([-r(y, b)] + [p(y, z, b) for z in R])
        base.append([-c(y, b)] + [p(z, y, b) for z in R])
    # Regularity of translations, proved from E1483 and its dual.
    for x, b, z in itertools.product(R, repeat=3):
        base.append([-c(x, b), -p(x, b, z), p(z, x, b)])
        base.append([-r(x, b), -p(b, x, z), p(x, z, b)])
    for x in R:
        for image in (r, c):
            base.append([-image(x, z) for z in R])
    clauses = list(base)
    for x in R:
        for image in (r, c):
            for sub in itertools.combinations(R, n - k + 1):
                clauses.append([image(x, z) for z in sub])
    image = set(range(k)) if zero else set(range(1, k + 1))
    for z in R:
        clauses.append([r(0, z) if z in image else -r(0, z)])
    for sub in itertools.combinations(R, k + 1):
        clauses.append([-c(0, z) for z in sub])
    clauses.append([p(0, 0, 0), p(0, 0, 1)] if zero else [p(0, 0, 1)])
    # Rows of rank three cannot be joined by either a row or column edge.
    if k == 3:
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, n - 3):
                    clauses.append([-large(x)] + [im(x, z) for z in sub])
            clauses.append([-p(x, x, x), large(x)])
        for x, y in itertools.product(R, repeat=2):
            clauses.append([-r(x, y), large(x), large(y)])
            clauses.append([-c(x, y), large(x), large(y)])
    for y in range(k + 1, n - 1):
        for z, w in itertools.product(range(k + 1), repeat=2):
            if z > w:
                clauses.append([-p(0, y, z), -p(0, y + 1, w)])
    # Semantically necessary cardinality bounds on both ends of every image edge.
    for threshold in [3, 4, 6]:
        flag = lambda x: a(4 + threshold, x, 0, 0)
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, n - threshold + 1):
                    clauses.append([-flag(x)] + [im(x, z) for z in sub])
    for x in R:
        clauses.append([-p(x, x, x), a(8, x, 0, 0)])
    for x, y in itertools.product(R, repeat=2):
        for im in (r, c):
            for t, u in [(3, 6), (4, 4), (6, 3)]:
                clauses.append([-im(x, y), a(4 + t, x, 0, 0), a(4 + u, y, 0, 0)])
    clauses = [cl for cl in clauses if not any(-l in cl for l in cl)]
    return clauses


def central_clauses(n, k, zero):
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    row = lambda x, z: 1 + ((n + x) * n + z) * n
    col = lambda x, z: 1 + ((3 * n + x) * n + z) * n
    old_sort = {(-p(0, y, z), -p(0, y + 1, w))
                for y in range(k + 1, n - 1)
                for z in range(k + 1) for w in range(z)}
    cs = [c for c in central_base(n, k, zero) if tuple(c) not in old_sort]
    for a, b in itertools.product(range(n), repeat=2):
        cs.extend([[-row(a, b), col(b, a)], [-col(b, a), row(a, b)]])
    for a, b, z in itertools.product(range(n), repeat=3):
        cs.extend([[-p(a, b, z), row(z, b)], [-p(a, b, z), col(z, a)]])
    for y in range(k if zero else k + 1, n - 1):
        c, d = col(0, y), col(0, y + 1)
        cs.append([c, -d])
        for z, w in itertools.product(range(k + 1), repeat=2):
            if w < z:
                cs.append([c, d, -p(0, y, z), -p(0, y + 1, w)])
            if w <= z:
                cs.append([-c, -d, -p(0, y, z), -p(0, y + 1, w)])
    cs.extend([-p(0, 1, z)] for z in range(3, n))
    return cs


def weak_central_clauses(n, k, inside):
    """E1486 square-row graph, with a chosen minimum-rank row at zero.

    This is the general base of spectrum_1486_ten.py, without its extra
    assumptions specific to the order-ten case split.
    """
    from itertools import product, combinations
    r = range(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    sq = lambda s: n**3 + 1 + s
    col = lambda x, a: n**3 + n + 1 + x * n + a
    row = lambda x, b: n**3 + n + n*n + 1 + x * n + b
    cs = []
    for x, y in product(r, repeat=2):
        vs = [p(x, y, z) for z in r]
        cs.append(vs)
        cs.extend([-a, -b] for a, b in combinations(vs, 2))
    for z, s in product(r, repeat=2):
        cs.append([-p(z, z, s), sq(s)])
    for s in r:
        cs.append([-sq(s)] + [p(z, z, s) for z in r])
    for x, s, b in product(r, repeat=3):
        cs.append([-sq(s), -p(x, s, b), row(x, b)])
    for x, y, a in product(r, repeat=3):
        cs.append([-p(y, x, a), col(x, a)])
    for x, a, b in product(r, repeat=3):
        cs.append([-row(x, b), -col(x, a), p(a, b, x)])
    for x, a, b, u in product(r, repeat=4):
        if a < b:
            cs.append([-row(x, a), -row(x, b), -row(a, u), -row(b, u)])
    for x in r:
        for sub in combinations(r, n-k+1):
            cs.append([row(x, b) for b in sub])
    for x, y, u in product(r, repeat=3):
        cs.append([-row(x, y), -row(y, u), p(x, u, y)])
    for s, t in product(r, repeat=2):
        cs.append([-sq(s), -p(s, s, t), p(t, t, s)])
    allowed = set(range(k)) if inside else set(range(1, k+1))
    cs.extend([row(0, b) if b in allowed else -row(0, b)] for b in r)
    return [c for c in cs if not any(-v in c for v in c)]


def run(law, n, family, seconds, output, rank=None, zero=False, seed=0, fixed=()):
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    if law == 1483:
        cs, nv = central_clauses(n, rank, zero), n**4
    elif law == 1486:
        cs, nv = weak_central_clauses(n, rank, zero), n**3+n+2*n*n
    elif law == 883:
        from spectrum_small_pair_search import encode
        nv, cs = encode(law, n, right=True)
    else:
        cs, nv = chain_clauses(law, n), variables(law, n)
    if family in ('idempotent', 'idempotent-commutative'):
        cs.extend([[p(x, x, x)] for x in range(n)])
    if family in ('commutative', 'idempotent-commutative'):
        cs.extend([-p(x, y, z), p(y, x, z)]
                  for x, y, z in itertools.product(range(n), repeat=3))
    if family == 'nonidempotent':
        cs.append([-p(0, 0, 0)])
    cs.extend([p(x, y, z)] for x, y, z in fixed)
    cnf = (f'p cnf {nv} {len(cs)}\n' +
           ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs)).encode()
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    cnf_path = output.with_suffix('.cnf')
    cnf_path.write_bytes(cnf)
    command = ['cadical', '--seed=' + str(seed), '-t', str(seconds), str(cnf_path)]
    start = time.monotonic()
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=seconds+30)
        stdout, stderr, code = result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = (exc.stdout or b'').decode() if isinstance(exc.stdout, bytes) else (exc.stdout or '')
        stderr, code = 'External wall-clock timeout', None
    record = dict(law=law, order=n, family=family, minimum_rank=rank,
                  zero_in_image=zero if law in (1483, 1486) else None,
                  seed=seed, budget=seconds, seconds=time.monotonic()-start,
                  fixed_cells=list(fixed),
                  status={10:'SAT', 20:'UNSAT'}.get(code, 'UNKNOWN'),
                  variables=nv, clauses=len(cs),
                  cnf_sha256=hashlib.sha256(cnf).hexdigest(),
                  command=command, table=None,
                  caveat='Exploratory search, not a Lean proof. Restricted UNSAT excludes only the specified family.')
    if law in (1483, 1486) and family == 'nonidempotent':
        record['scope'] = 'The chosen minimum-rank row is non-idempotent; not all non-idempotent magmas.'
    output.with_suffix('.log').write_text(stdout + stderr)
    if code == 10:
        vals = {int(w) for line in stdout.splitlines() if line.startswith('v ')
                for w in line.split()[1:] if int(w)>0}
        table = [[next(z for z in range(n) if p(x,y,z) in vals)
                  for y in range(n)] for x in range(n)]
        lhs, rhs = load_equations()[law-1]
        assert satisfies(lhs, rhs, [z for row in table for z in row], n)
        record['table'] = table
        record['independent_original_law_check'] = True
        record['idempotent'] = all(table[x][x]==x for x in range(n))
        record['commutative'] = all(table[x][y]==table[y][x] for x,y in itertools.product(range(n),repeat=2))
    output.with_suffix('.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'E{law}/{n} {family} rank={rank} zero={zero}: {record["status"]} ({record["seconds"]:.2f}s)', flush=True)
    return record


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('law', type=int)
    ap.add_argument('order', type=int)
    ap.add_argument('--family', choices=('all', 'idempotent', 'commutative', 'idempotent-commutative', 'nonidempotent'), default='all')
    ap.add_argument('--seconds', type=int, default=900)
    ap.add_argument('--rank', type=int)
    ap.add_argument('--zero', action='store_true')
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--fixed', nargs=3, action='append', type=int, default=[],
                    metavar=('ROW', 'COLUMN', 'VALUE'))
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.order <= 0 or args.seconds <= 0 or args.order == 10:
        ap.error('Positive order and timeout required; this campaign excludes order ten.')
    if args.law in (1483, 1486) and (args.rank is None or not 2 <= args.rank < args.order):
        ap.error('The graph searches require --rank between 2 and order-1.')
    if any(not 0 <= v < args.order for cell in args.fixed for v in cell):
        ap.error('Fixed cell coordinates and values must lie in the carrier.')
    run(args.law, args.order, args.family, args.seconds, args.output, args.rank, args.zero,
        args.seed, args.fixed)


if __name__ == '__main__':
    main()


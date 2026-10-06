#!/usr/bin/env python3
"""Search E667 magmas with a specified regular group of automorphisms.

The profile h defines x*y=x h(x^-1 y). One group element h(1) specifies
all squares. UNSAT excludes only this regular-action construction class.
Every positive table is independently checked against the original law.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
import time

# pandas can use pyarrow optionally; the host's optional pyarrow binary is
# incompatible with its NumPy installation. This search does not use it.
sys.modules.setdefault('pyarrow', None)
from ortools.sat.python import cp_model


def table_from_elements(elements, mul):
    index = {x: i for i, x in enumerate(elements)}
    return [[index[mul(x, y)] for y in elements] for x in elements]


def cyclic(n):
    return [[(x+y) % n for y in range(n)] for x in range(n)]


def product(a, b):
    m, n = len(a), len(b)
    return [[a[x//n][y//n]*n+b[x % n][y % n] for y in range(m*n)]
            for x in range(m*n)]


def group(name):
    if name in ['C3rtC8', 'C3rtD8']:
        p = group('C8' if name == 'C3rtC8' else 'D8')
        es = [(a,b) for b in range(8) for a in range(3)]
        return table_from_elements(es, lambda x,y:
            ((x[0]+(-1)**(x[1] % 2)*y[0]) % 3, p[x[1]][y[1]]))
    if 'x' in name:
        a, b = name.split('x', 1)
        return product(group(a), group(b))
    if name.startswith('C'):
        return cyclic(int(name[1:]))
    if name.startswith('Dic'):
        m = int(name[3:]) // 2
        assert m % 2 == 0
        es = [(a,b) for b in range(2) for a in range(m)]
        return table_from_elements(es, lambda x,y: ((x[0]+(-1)**x[1]*y[0]+(m//2)*x[1]*y[1]) % m,
                                                     (x[1]+y[1]) % 2))
    if name.startswith('D'):
        m = int(name[1:]) // 2
        es = [(a,b) for b in range(2) for a in range(m)]
        return table_from_elements(es, lambda x,y: ((x[0]+(-1)**x[1]*y[0]) % m,
                                                     (x[1]+y[1]) % 2))
    if name == 'Q8':
        es = [(a,b) for b in range(2) for a in range(4)]
        return table_from_elements(es, lambda x,y: ((x[0]+(-1)**x[1]*y[0]+2*x[1]*y[1]) % 4,
                                                     (x[1]+y[1]) % 2))
    if name in ['A4', 'S4', 'A5']:
        degree = int(name[1:])
        es = [x for x in itertools.permutations(range(degree)) if name[0] == 'S' or
              sum(x[i] > x[j] for i in range(degree) for j in range(i+1,degree)) % 2 == 0]
        return table_from_elements(es, lambda x,y: tuple(x[y[i]] for i in range(degree)))
    if name == 'SL2F3':
        q = group('Q8')
        phi = [0, 4, 2, 6, 5, 1, 7, 3]  # i -> j -> k -> i
        es = [(a,b) for b in range(3) for a in range(8)]
        def mul(x, y):
            a = y[0]
            for _ in range(x[1]):
                a = phi[a]
            return q[x[0]][a], (x[1]+y[1]) % 3
        return table_from_elements(es, mul)
    if name in ['F21', 'F20']:
        p, k, r = (7, 3, 2) if name == 'F21' else (5, 4, 2)
        es = [(a,b) for b in range(k) for a in range(p)]
        return table_from_elements(es, lambda x,y: ((x[0]+pow(r,x[1],p)*y[0]) % p,
                                                     (x[1]+y[1]) % k))
    if name == 'F75':
        es = [(a,b,c) for c in range(3) for a in range(5) for b in range(5)]
        def mul(x, y):
            a,b = y[:2]
            for _ in range(x[2]):
                a,b = -b, a-b
            return ((x[0]+a) % 5, (x[1]+b) % 5, (x[2]+y[2]) % 3)
        return table_from_elements(es, mul)
    if name.startswith('F'):
        n = int(name[1:])
        p = n//3
        assert n == 3*p and p % 3 == 1
        assert all(p % d for d in range(2, int(p**0.5)+1))
        r = next(r for r in range(2,p) if pow(r,3,p) == 1)
        es = [(a,b) for b in range(3) for a in range(p)]
        return table_from_elements(es, lambda x,y:
            ((x[0]+pow(r,x[1],p)*y[0]) % p, (x[1]+y[1]) % 3))
    if name == 'H27':
        es = list(itertools.product(range(3), repeat=3))
        return table_from_elements(es, lambda x,y: ((x[0]+y[0]) % 3,
                (x[1]+y[1]) % 3, (x[2]+y[2]+x[0]*y[1]) % 3))
    raise ValueError(name)


def validate_group(g):
    n = len(g)
    assert g[0] == list(range(n))
    assert [g[x][0] for x in range(n)] == list(range(n))
    assert all(sorted(row) == list(range(n)) for row in g)
    assert all(g[g[x][y]][z] == g[x][g[y][z]]
               for x in range(n) for y in range(n) for z in range(n))
    return [g[x].index(0) for x in range(n)]


def properties(q):
    n = len(q)
    assert all(q[y][q[x][q[q[x][x]][y]]] == x for x in range(n) for y in range(n))
    assert all(sorted(row) == list(range(n)) for row in q)
    assert all(sorted(q[x][y] for x in range(n)) == list(range(n)) for y in range(n))
    medial_failure = next(((x,y,z,w) for x in range(n) for y in range(n)
                          for z in range(n) for w in range(n)
                          if q[q[x][y]][q[z][w]] != q[q[x][z]][q[y][w]]), None)
    return dict(idempotents=[x for x in range(n) if q[x][x] == x],
                commutative=all(q[x][y] == q[y][x] for x in range(n) for y in range(n)),
                medial=medial_failure is None, medial_failure=medial_failure,
                square_hom=all(q[q[x][y]][q[x][y]] == q[q[x][x]][q[y][y]]
                               for x in range(n) for y in range(n)))


def solve(name, seconds=30, diagonal='any', nonmedial=False, seed=1):
    g = group(name)
    n = len(g)
    inv = validate_group(g)
    m = cp_model.CpModel()
    h = [m.NewIntVar(0,n-1,f'h_{i}') for i in range(n)]
    m.AddAllDifferent(h)
    flat = sum(g, [])
    def elem(xs, ix, label):
        out = m.NewIntVar(0,n-1,label)
        m.AddElement(ix,xs,out)
        return out
    def mul(a,b,label):
        return elem(flat,n*a+b,label)
    delta = [elem(g[inv[t]],h[t],f'delta_{t}') for t in range(n)]
    m.AddAllDifferent(delta)
    if diagonal == 'idempotent':
        m.Add(h[0] == 0)
    elif diagonal == 'free':
        m.Add(h[0] != 0)
    d = h[0]
    di = elem(inv,d,'inv_diagonal')
    for t in range(n):
        if diagonal == 'idempotent':
            # h(1)=1 reduces the exact profile criterion to three lookups.
            e = elem(h,h[t],f'e_{t}')
            f = elem(g[inv[t]],e,f'f_{t}')
            m.AddElement(f,h,inv[t])
            continue
        a = mul(di,t,f'a_{t}')
        b = elem(h,a,f'b_{t}')
        c = mul(d,b,f'c_{t}')
        e = elem(h,c,f'e_{t}')
        f = elem(g[inv[t]],e,f'f_{t}')
        m.AddElement(f,h,inv[t])
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.random_seed = seed
    start = time.monotonic()
    skipped = 0
    while True:
        remain = seconds-(time.monotonic()-start)
        if remain <= 0:
            status = 'UNKNOWN'
            break
        solver.parameters.max_time_in_seconds = remain
        st = solver.Solve(m)
        status = solver.StatusName(st)
        if st not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
            break
        profile = [solver.Value(x) for x in h]
        q = [[g[x][profile[g[inv[x]][y]]] for y in range(n)] for x in range(n)]
        ps = properties(q)
        if nonmedial and ps['medial']:
            skipped += 1
            m.AddForbiddenAssignments(h,[profile])
            continue
        out = dict(profile=profile,table=q,properties=ps)
        break
    else:
        raise AssertionError('unreachable')
    result = dict(group=name,order=n,diagonal=diagonal,require_nonmedial=nonmedial,
                  status=status,seconds_limit=seconds,elapsed=time.monotonic()-start,
                  seed=seed,workers=1,skipped_medial_profiles=skipped,
                  scope='regular group action; not unrestricted E667')
    if status in ['OPTIMAL','FEASIBLE']:
        result.update(out)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('group')
    p.add_argument('--seconds',type=float,default=30)
    p.add_argument('--diagonal',choices=['any','idempotent','free'],default='any')
    p.add_argument('--nonmedial',action='store_true')
    p.add_argument('--seed',type=int,default=1)
    p.add_argument('--output',type=Path)
    a = p.parse_args()
    out = solve(a.group,a.seconds,a.diagonal,a.nonmedial,a.seed)
    text = json.dumps(out,indent=2)+'\n'
    if a.output:
        a.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()

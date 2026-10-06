#!/usr/bin/env python3
"""One-hot SAT search for regular-action E667 models with fixed square value.

The exact criterion h(x^-1 h(d h(d^-1 x)))=x^-1 uses three-way propagation, with
permutation constraints for both h(x) and x^-1 h(x). UNSAT excludes only
the specified group-action construction and square value d=h(1). Positive
tables are checked directly. The default d=1 gives idempotent models.
"""
import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_regular import group, validate_group, properties


def formula(name, symmetry=True, diagonal=0):
    g = group(name)
    n = len(g)
    inv = validate_group(g)
    assert 0 <= diagonal < n
    d = diagonal
    p = lambda x,y: 1+x*n+y
    cs = []
    def one(vs):
        cs.append(vs)
        cs.extend([-a,-b] for a,b in combinations(vs,2))
    for x in range(n):
        one([p(x,y) for y in range(n)])
        one([p(y,x) for y in range(n)])
        one([p(y,g[y][x]) for y in range(n)])
    cs.append([p(0,d)])
    for x in range(n):
        for y in range(n):
            for z in range(n):
                a,b,c = p(g[inv[d]][x],y),p(g[d][y],z),p(g[inv[x]][z],inv[x])
                cs.extend([[-a,-b,c],[-a,-c,b],[-b,-c,a]])
    if symmetry and name.startswith('C') and name[1:].isdigit():
        # Select a conjugate whose h(1) is minimal under unit multipliers.
        from math import gcd
        for u in range(2,n):
            if gcd(u,n) != 1:
                continue
            if u*d % n != d:
                continue
            ui = pow(u,-1,n)
            for a in range(n):
                for b in range(n):
                    if a > ui*b % n:
                        cs.append([-p(1,a),-p(u,b)])
    return g,inv,cs


def solve(name,seconds,workdir,diagonal=0):
    g,inv,cs = formula(name,diagonal=diagonal)
    n = len(g)
    workdir.mkdir(parents=True,exist_ok=True)
    stem = name+(f'-d{diagonal}' if diagonal else '')
    path = workdir/(stem+'.cnf')
    with path.open('w') as f:
        f.write(f'p cnf {n*n} {len(cs)}\n')
        for c in cs:
            f.write(' '.join(map(str,c))+' 0\n')
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    count = len(cs)
    del cs
    start = time.monotonic()
    cp = subprocess.run(['cadical','--quiet','-t',str(seconds),str(path)],
                        capture_output=True,text=True)
    (workdir/(stem+'.log')).write_text(cp.stdout+cp.stderr)
    out = dict(group=name,order=n,diagonal='free' if diagonal else 'idempotent',
               diagonal_value=diagonal,seconds_limit=seconds,
               elapsed=time.monotonic()-start,variables=n*n,clauses=count,
               cnf_sha256=digest,status={10:'SAT',20:'UNSAT'}.get(cp.returncode,'UNKNOWN'),
               scope='regular action of the specified group, with the specified square value')
    if cp.returncode == 10:
        vals = {int(v) for line in cp.stdout.splitlines() if line.startswith('v ')
                for v in line.split()[1:]}
        h = [next(y for y in range(n) if 1+x*n+y in vals) for x in range(n)]
        table = [[g[x][h[g[inv[x]][y]]] for y in range(n)] for x in range(n)]
        ps = properties(table)
        assert ps['idempotents'] == ([] if diagonal else list(range(n)))
        out.update(profile=h,table=table,properties=ps)
    path.unlink()
    (workdir/(stem+'.json')).write_text(json.dumps(out,indent=2)+'\n')
    return {k:v for k,v in out.items() if k not in ('table','profile','properties')}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('group')
    p.add_argument('--seconds',type=int,default=180)
    p.add_argument('--workdir',type=Path,required=True)
    p.add_argument('--diagonal-value',type=int,default=0,
                   help='Index d of h(1); index zero is the group identity')
    a = p.parse_args()
    print(solve(a.group,a.seconds,a.workdir,a.diagonal_value))

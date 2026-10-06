#!/usr/bin/env python3
"""Search idempotent E667 isotopes of explicit twenty-point loop bases.

UNSAT concerns the specified isotope class, not all magmas of order twenty.
The Boolean eight-point group is available as a positive encoding control.
"""
import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_nonlinear_isotopes import formula

ROOT = Path(__file__).resolve().parents[1]


def base(name):
    if name == 'boolean8':
        return [[i ^ j for j in range(8)] for i in range(8)]
    if name == 's3_20':
        return json.loads((ROOT/'data/spectrum/667_nonlinear_constructions.json').read_text())[
            'nonabelian_group_design']['table']
    if name == 'steiner20':
        q = [[None]*20 for _ in range(20)]
        for x in range(20):
            q[x][19] = q[19][x] = x
            q[x][x] = 19
        for b in [[0,1,4], [0,2,9], [0,5,11]]:
            for t in range(19):
                block = [(a+t) % 19 for a in b]
                for x,y in combinations(block,2):
                    assert q[x][y] is None
                    q[x][y] = q[y][x] = next(z for z in block if z not in (x,y))
        assert all(None not in row for row in q)
        return q
    raise ValueError(name)


def solve(name, seconds, workdir):
    table = base(name)
    n = len(table)
    top, clauses, (p,a,b) = formula(table)
    clauses.extend([[p(x,x,x)] for x in range(n)])
    workdir.mkdir(parents=True, exist_ok=True)
    cnf = workdir/(name+'.cnf')
    text = f'p cnf {top} {len(clauses)}\n'+''.join(
        ' '.join(map(str,c))+' 0\n' for c in clauses)
    cnf.write_text(text)
    start = time.monotonic()
    cp = subprocess.run(['cadical','--quiet','-t',str(seconds),str(cnf)],
                        capture_output=True,text=True)
    (workdir/(name+'.solver.log')).write_text(cp.stdout+cp.stderr)
    out = dict(base=name, order=n, seconds_limit=seconds,
               elapsed=time.monotonic()-start, variables=top, clauses=len(clauses),
               cnf_sha256=hashlib.sha256(text.encode()).hexdigest(),
               status={10:'SAT',20:'UNSAT'}.get(cp.returncode,'UNKNOWN'),
               scope='idempotent isotopes of this explicit base only', base_table=table)
    if cp.returncode == 10:
        vals = {int(v) for line in cp.stdout.splitlines() if line.startswith('v ')
                for v in line.split()[1:]}
        q = [[next(z for z in range(n) if p(x,y,z) in vals)
              for y in range(n)] for x in range(n)]
        assert all(q[x][x] == x for x in range(n))
        assert all(q[y][q[x][q[q[x][x]][y]]] == x for x in range(n) for y in range(n))
        out['table'] = q
        out['alpha'] = [next(z for z in range(n) if a(x,z) in vals) for x in range(n)]
        out['beta'] = [next(z for z in range(n) if b(x,z) in vals) for x in range(n)]
        assert all(q[x][y] == table[out['alpha'][x]][out['beta'][y]]
                   for x in range(n) for y in range(n))
    cnf.unlink()
    (workdir/(name+'.json')).write_text(json.dumps(out,indent=2)+'\n')
    return {k:v for k,v in out.items() if k not in ('table','base_table','alpha','beta')}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('base',choices=['boolean8','s3_20','steiner20'])
    p.add_argument('--seconds',type=int,default=120)
    p.add_argument('--workdir',type=Path,required=True)
    a = p.parse_args()
    print(solve(a.base,a.seconds,a.workdir))

#!/usr/bin/env python3
"""Search finite E667 using its left-division table, with no auxiliary table.

For a Latin operation q, let D(x) be the unique d with q(x,d)=x. Its left
division p satisfies E667 iff R_x L_D(x) L_x = identity for every x.
UNSAT is external evidence for the selected case, never a Lean proof.
"""
import argparse
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_generate import load_equations, satisfies


def encode(n, mode='all', propagation=True):
    r = range(n)
    p = lambda x,y,z: 1+(x*n+y)*n+z
    cs=[]
    for x,y in product(r,repeat=2):
        for vals in ([p(x,y,z) for z in r], [p(x,z,y) for z in r],
                     [p(z,x,y) for z in r]):
            cs.append(vals)
            cs.extend([-a,-b] for a,b in combinations(vals,2))
    for x,d,y,u,v in product(r,repeat=5):
        # D(x)=d, q(x,y)=u, q(d,u)=v, q(v,x)=y.
        di,a,b,c=p(x,d,x),p(x,y,u),p(d,u,v),p(v,x,y)
        cs.append([-di,-a,-b,c])
        if propagation:
            cs.append([-di,-a,b,-c])
            cs.append([-di,a,-b,-c])
    if n%3==0:
        # Constant original square = right identity for q.
        for d in r:cs.append([-p(x,d,x) for x in r])
    if n==12:
        cs.append([-p(x,x,x) for x in r])
        # A right identity in the original table = constant diagonal for q.
        for e in r:cs.append([-p(x,x,e) for x in r])
    for x,a,b in product(r,repeat=3):
        cs.append([-p(x,x,a),-p(x,a,b),-p(x,b,x),p(x,x,x)])
    for x,a in product(r,repeat=2):
        cs.append([-p(x,x,a),-p(x,a,x),p(a,a,a)])
    for e,x,y in product(r,repeat=3):
        cs.append([-p(e,e,e),-p(x,e,x),-p(e,x,y),p(e,y,x)])
        cs.append([-p(e,e,e),-p(e,x,y),-p(e,y,x),p(x,e,x)])
        cs.append([-p(e,e,e),-p(x,e,x),-p(e,x,y),p(y,e,y)])
    if mode=='idempotent-free':cs.extend([[-p(x,x,x)] for x in r])
    elif mode=='one-idempotent':cs.append([p(0,0,0)])
    elif mode!='all':raise ValueError(mode)
    cs=[sorted(set(c)) for c in cs if not any(-x in c for x in c)]
    return n**3,cs


def check_encoding(table):
    n=len(table)
    assert satisfies(*load_equations()[666],sum(table,[]),n)
    q=[[row.index(y) for y in range(n)] for row in table]
    _,cs=encode(n)
    positive={1+(x*n+y)*n+q[x][y] for x,y in product(range(n),repeat=2)}
    assert all(any((v>0)==(abs(v) in positive) for v in c) for c in cs)
    return len(cs)


def solve(n,mode,cycles,seconds,workdir,seed=1):
    workdir.mkdir(parents=True,exist_ok=True)
    tag=mode+'-'+('-'.join(map(str,cycles)) if cycles else 'all')
    stem=workdir/tag
    top,cs=encode(n,mode)
    if cycles:
        assert sum(cycles)==n and min(cycles)>0
        row=[]
        for k in cycles:
            s=len(row)
            row.extend(list(range(s+1,s+k))+[s])
        cs.extend([[1+y*n+z] for y,z in enumerate(row)])
    path=stem.with_suffix('.cnf')
    with path.open('w') as out:
        out.write(f'p cnf {top} {len(cs)}\n')
        for c in cs:out.write(' '.join(map(str,c))+' 0\n')
    record=dict(order=n,mode=mode,cycles=cycles,variables=top,clauses=len(cs),
                cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                seconds_limit=seconds,seed=seed,
                scope='E667 left-division presentation with specified first-row cycle shape',
                proof_status='external search; no Lean replay')
    del cs
    start=time.monotonic()
    cp=subprocess.run(['cadical','-t',str(seconds),f'--seed={seed}',str(path)],capture_output=True,text=True)
    stem.with_suffix('.log').write_text(cp.stdout+cp.stderr)
    record.update(status={10:'SAT',20:'UNSAT'}.get(cp.returncode,'UNKNOWN'),
                  elapsed=time.monotonic()-start,exit_code=cp.returncode)
    if cp.returncode==10:
        vals={int(x) for line in cp.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
        q=[[next(z for z in range(n) if 1+(x*n+y)*n+z in vals) for y in range(n)] for x in range(n)]
        table=[[row.index(y) for y in range(n)] for row in q]
        assert satisfies(*load_equations()[666],sum(table,[]),n)
        record.update(table=table,division_table=q,verified_original_E667=True)
    stem.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print({k:v for k,v in record.items() if k not in ['table','division_table']},flush=True)
    return record


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=12)
    ap.add_argument('--mode',choices=['all','one-idempotent','idempotent-free'],default='one-idempotent')
    ap.add_argument('--cycles',type=lambda s:tuple(map(int,s.split(','))))
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--workdir',type=Path,required=True)
    args=ap.parse_args()
    solve(args.order,args.mode,args.cycles,args.seconds,args.workdir,args.seed)

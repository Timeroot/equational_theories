#!/usr/bin/env python3
"""Cyclic E229 completion with a freely refillable idempotent hole.

The q moving points form one automorphism orbit; p fixed points form a
subquasigroup. Sort their translation shifts and normalize the first to 1.
This is an existence normalization: hole multiplication is independently
replaceable, so no automorphism of the chosen hole table is assumed.
Only positive tables are model certificates. UNSAT concerns this template.
"""
import argparse
from itertools import combinations
import hashlib
import json
from pathlib import Path
import subprocess
import time
from pysat.card import CardEnc, EncType
from spectrum_63_bennett import prime
from spectrum_667_idempotent_search import checked_table


def encode(q, p, extra=True):
    assert q > 2 and all(q % d for d in range(2, int(q**.5)+1))
    assert 0 < p < q
    n=q+p
    inv2=pow(2,-1,q)
    top=q*n+p*q
    cs=[]
    def f(t,z): return 1+t*n+z
    def a(i,s): return 1+q*n+i*q+s
    def left(t,z):
        if t<q: return f(t,z)
        return a(t-q,(-z*inv2)%q) if z<q else False
    def right(t,z):
        if t<q: return f((-t)%q,(z-t)%q if z<q else z)
        return a(t-q,z) if z<q else False
    def neg(x): return not x if type(x) is bool else -x
    def add(ls):
        if any(x is True for x in ls):return
        ls=set(x for x in ls if x is not False)
        if any(-x in ls for x in ls):return
        cs.append(sorted(ls))
    def one(ls):
        nonlocal top
        fixed=sum(x is True for x in ls)
        vs=[x for x in ls if type(x) is int]
        if fixed>1:add([])
        elif fixed:
            for x in vs:add([-x])
        else:
            c=CardEnc.equals(vs,1,top_id=top,encoding=EncType.seqcounter)
            top=max(top,c.nv)
            cs.extend(c.clauses)
    for t in range(n):one([left(t,z) for z in range(n)])
    for z in range(n):
        one([left(t,z) for t in range(n)])
        one([right(t,z) for t in range(n)])
    add([f(0,0)])
    for t in range(1,n):add([neg(left(t,t))])
    for t,u in combinations(range(n),2):add([neg(left(t,u)),neg(left(u,t))])
    add([a(0,1)])
    for i in range(p):
        for s in range(q):
            if s < i+1 or s > q-p+i:add([-a(i,s)])
        if i:
            for s in range(q):
                for t in range(s+1):add([-a(i-1,s),-a(i,t)])
    for t in range(n):
        for u in range(n):
            av=left(t,u)
            for v in range(n):
                bv,cv=left(u,v),right(v,t)
                add([neg(av),neg(bv),cv])
                add([neg(av),bv,neg(cv)])
                add([av,neg(bv),neg(cv)])
    if extra:
        # If H_i is the moving input sent to fixed point i, then
        # F(A_i)=H_i, F(-2A_i)=-H_i, F(2A_i)=H_i+2A_i.
        for i in range(p):
            for s in range(1,q):
                for t in range(1,q):
                    for u,v in [(s,t),((-2*s)%q,(-t)%q),((2*s)%q,(t+2*s)%q)]:
                        add([-a(i,s),-f(t,q+i),f(u,v)])
    return top,cs


def expand(q,p,values):
    n=q+p
    A=[next(s for s in range(q) if 1+q*n+i*q+s in values) for i in range(p)]
    F=[next(z for z in range(n) if 1+t*n+z in values) for t in range(q)]
    P=prime(p) if p>1 else [[0]]
    checked_table(P)
    def op(x,y):
        if x>=q:
            return q+P[x-q][y-q] if y>=q else (y+A[x-q])%q
        if y>=q:return (x-2*A[y-q])%q
        z=F[(y-x)%q]
        return (x+z)%q if z<q else z
    table=[[op(x,y) for y in range(n)] for x in range(n)]
    converted=checked_table(table)
    assert A[0]==1 and all(A[i]<A[i+1] for i in range(p-1))
    assert all(table[x][y]>=q for x in range(q,n) for y in range(q,n))
    return dict(shifts=A,profile=F,e229_table=table,e63_table=converted)


def solve(q,p,seconds,workdir,seed=1,extra=True):
    workdir.mkdir(parents=True,exist_ok=True)
    stem=workdir/f'{q}-{p}-seed{seed}'
    top,cs=encode(q,p,extra)
    path=stem.with_suffix('.cnf')
    with path.open('w') as out:
        out.write(f'p cnf {top} {len(cs)}\n')
        for c in cs:out.write(' '.join(map(str,c))+' 0\n')
    record=dict(order=q+p,cycle_length=q,hole_size=p,seed=seed,
                variables=top,clauses=len(cs),cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                seconds_limit=seconds,extra_propagation=extra,
                scope='idempotent E229 with one prime automorphism orbit and a fixed hole',
                normalization='sorted hole shifts, first shift 1; independently refillable hole')
    del cs
    start=time.monotonic()
    cp=subprocess.run(['cadical','-t',str(seconds),f'--seed={seed}',str(path)],capture_output=True,text=True)
    stem.with_suffix('.log').write_text(cp.stdout+cp.stderr)
    record.update(status={10:'VERIFIED_MODEL',20:'UNSAT_RESTRICTED'}.get(cp.returncode,'UNKNOWN'),
                  elapsed=time.monotonic()-start,exit_code=cp.returncode)
    if cp.returncode==10:
        values={int(x) for line in cp.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
        record.update(expand(q,p,values))
    stem.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    return {k:v for k,v in record.items() if k not in ['e229_table','e63_table','profile']}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('cycle_length',type=int)
    ap.add_argument('hole_size',type=int)
    ap.add_argument('--seconds',type=int,default=300)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--workdir',type=Path,required=True)
    ap.add_argument('--no-extra',action='store_true')
    a=ap.parse_args()
    print(solve(a.cycle_length,a.hole_size,a.seconds,a.workdir,a.seed,not a.no_extra))

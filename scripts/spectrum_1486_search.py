#!/usr/bin/env python3
"""Exploratory E1486 finite-model search; UNSAT is not a Lean certificate.

Example: timeout 60 python3 scripts/spectrum_1486_search.py 8
The equation is encoded by square-image and column-image containment.
Diagonal normalization f(0,0) in {0,1} only relabels the carrier.
SAT models are independently checked on every law instance before saving.
"""
import sys,time,json,itertools
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
n=int(sys.argv[1]);start=time.time();pool=IDPool();solver=Solver(name='cadical195')
p=lambda x,y,z:pool.id(('p',x,y,z))
sq=lambda z:pool.id(('s',z))
col=lambda x,a:pool.id(('col',x,a))
left=lambda x,b:pool.id(('left',x,b))
for x,y in itertools.product(range(n),repeat=2):
 for c in CardEnc.equals([p(x,y,z)for z in range(n)],1,vpool=pool,encoding=EncType.seqcounter):solver.add_clause(c)
solver.add_clause([p(0,0,0),p(0,0,1)])
for z,s in itertools.product(range(n),repeat=2):solver.add_clause([-p(z,z,s),sq(s)])
for s in range(n):solver.add_clause([-sq(s)]+[p(z,z,s)for z in range(n)])
for x,s,b in itertools.product(range(n),repeat=3):solver.add_clause([-sq(s),-p(x,s,b),left(x,b)])
for x,y,a in itertools.product(range(n),repeat=3):solver.add_clause([-p(y,x,a),col(x,a)])
for x,a,b in itertools.product(range(n),repeat=3):solver.add_clause([-left(x,b),-col(x,a),p(a,b,x)])
print(n,'encoded',pool.top,solver.nof_clauses(),'seconds',time.time()-start,flush=True)
status=solver.solve();print(n,status,time.time()-start,flush=True)
if status:
 m=set(solver.get_model());t=[[next(z for z in range(n)if p(x,y,z)in m)for y in range(n)]for x in range(n)]
 assert all(t[t[y][x]][t[x][t[z][z]]]==x for x,y,z in itertools.product(range(n),repeat=3))
 json.dump({'order':n,'table':t},open(f'/tmp/e1486-model-{n}.json','w'))

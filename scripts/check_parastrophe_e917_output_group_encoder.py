#!/usr/bin/env python3
"""Check the fixed-output encoder against the literal E917 candidate on all Latin squares through order four."""
import sys,itertools
sys.path.insert(0,'scripts')
from parastrophe_e917_output_group_search import encode
from pysat.solvers import Solver

def latin(n):
 rows=list(itertools.permutations(range(n)))
 def go(t):
  if len(t)==n:yield t;return
  for r in rows:
   if all(r[k] not in [s[k]for s in t]for k in range(n)):yield from go(t+[r])
 yield from go([])
count=encoded=positives=fixed_checks=0
for n in [2,3,4]:
 for m in latin(n):
  count+=1;q=[m[m[x][m[x][x]]][x]for x in range(n)];u=[m[x][q[x]]for x in range(n)]
  fs=[[m[y][m[q[x]][m[x][y]]]for y in range(n)]for x in range(n)]
  actual=all(m[m[u[y]][v]][m[q[x]][m[x][fs[m[y][v]][z]]]]==x for x,y,v,z in itertools.product(range(n),repeat=4))
  positives+=actual
  a=[r[0]for r in fs]
  if sorted(a)!=list(range(n)):
   assert not actual;continue
  b=[0]*n
  for y in range(n):b[m[0][y]]=m[u[0]][y]
  assert sorted(b)==list(range(n))
  cnf,mt,_=encode(a,b,require_defect=False)
  with Solver(name='cadical195',bootstrap_with=cnf)as s:
   ans=s.solve(assumptions=[mt[x][y][m[x][y]]for x,y in itertools.product(range(n),repeat=2)])
   assert ans==actual,(m,ans,actual)
  encoded+=1
  if sorted(u)==list(range(n)):
   for pinned,expected in [(u,actual)]+([([(v+1)%n for v in u],False)]if actual else[]):
    cnf,mt,_=encode(a,b,require_defect=False,fixed_unit=pinned)
    with Solver(name='cadical195',bootstrap_with=cnf)as solver:
     answer=solver.solve(assumptions=[mt[x][y][m[x][y]]for x,y in itertools.product(range(n),repeat=2)])
     assert answer==expected,(m,pinned,answer,expected)
    fixed_checks+=1
print(count, 'Latin tables,',encoded,'SAT comparisons,',positives,'literal positives;',fixed_checks,'fixed-unit checks')

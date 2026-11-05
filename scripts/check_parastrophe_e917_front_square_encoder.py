#!/usr/bin/env python3
"""Cross-check the E917 double-crossed encoder on every Latin square of order <=4.

The reference evaluator expands the literal five-variable identity. It does
not call the normalized criterion encoded in the SAT search. This validates
the research encoder; it is not a Lean proof about higher orders.
"""
import itertools,sys,time
sys.path.insert(0,'scripts')
from parastrophe_e917_front_square_search import encode
from pysat.solvers import Solver

def literal(m):
 n=len(m);q=[m[m[x][m[x][x]]][x]for x in range(n)];u=[m[x][q[x]]for x in range(n)]
 for x,y,v,z,w in itertools.product(range(n),repeat=5):
  f=m[z][m[q[m[y][v]]][m[m[y][v]][z]]]
  f=m[w][m[q[f]][m[f][w]]]
  if m[m[u[y]][v]][m[q[x]][m[x][f]]]!=x:return False
 return True

def latin(n):
 rows=list(itertools.permutations(range(n)))
 def go(t):
  if len(t)==n:yield t;return
  for r in rows:
   if all(r[k] not in [s[k]for s in t]for k in range(n)):
    yield from go(t+[r])
 yield from go([])
for n in [2,3,4]:
 count=positive=encoded=0;engines={};lex_engines={};lex_checked=set()
 for m in latin(n):
  count+=1;actual=literal(m);positive+=actual
  q=[m[m[x][m[x][x]]][x]for x in range(n)];u=tuple(m[x][q[x]]for x in range(n))
  if sorted(u)!=list(range(n)):
   assert not actual
   continue
  if u not in engines:
   cnf,mt,fs,U=encode(n,1,u)
   engines[u]=(Solver(name='cadical195',bootstrap_with=cnf),mt)
  s,mt=engines[u]
  ans=s.solve(assumptions=[mt[x][y][m[x][y]]for x,y in itertools.product(range(n),repeat=2)])
  assert ans==actual,(n,m,u,ans,actual)
  encoded+=1
  # Relabel uniform cycles, then take the full centralizer-orbit minimum.
  # That minimum must survive every generator inequality in the SAT encoder.
  unseen=set(range(n));cycles=[]
  while unseen:
   cyc=[];x=min(unseen)
   while x not in cyc:cyc.append(x);unseen.remove(x);x=u[x]
   cycles.append(cyc)
  period=len(cycles[0])
  if any(len(c)!=period for c in cycles):
   assert not actual
   continue
  lab={x:i*period+j for i,c in enumerate(cycles)for j,x in enumerate(c)}
  inv=[next(x for x in range(n)if lab[x]==k)for k in range(n)]
  tab=[[lab[m[inv[x]][inv[y]]]for y in range(n)]for x in range(n)]
  U=[x//period*period+(x+1)%period for x in range(n)]
  conjugates=[]
  for perm in itertools.permutations(range(n)):
   if any(perm[U[x]]!=U[perm[x]]for x in range(n)):continue
   pinv=[perm.index(x)for x in range(n)]
   conjugates.append(tuple(perm[tab[pinv[x]][pinv[y]]]for x,y in itertools.product(range(n),repeat=2)))
  smallest=min(conjugates)
  if (period,smallest) in lex_checked:continue
  if period not in lex_engines:
   cnf,lt,_,_=encode(n,period,symmetry=True)
   lex_engines[period]=(Solver(name='cadical195',bootstrap_with=cnf),lt)
  solver,lt=lex_engines[period]
  answer=solver.solve(assumptions=[lt[x][y][smallest[n*x+y]]for x,y in itertools.product(range(n),repeat=2)])
  # The counterexample search excludes a=id, hence excludes all images.
  image=all(u[x]==x and m[y][m[q[x]][m[x][y]]]==x
            for x,y in itertools.product(range(n),repeat=2))
  assert answer==(actual and not image),('symmetry',n,m,u,answer,actual,image)
  lex_checked.add((period,smallest))
 for s,mt in engines.values():s.delete()
 for s,mt in lex_engines.values():s.delete()
 print(n,count,'Latin tables;',positive,'literal positives;',encoded,'SAT comparisons;',len(lex_checked),'symmetry representatives',flush=True)

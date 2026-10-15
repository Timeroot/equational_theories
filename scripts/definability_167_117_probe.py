#!/usr/bin/env python3
"""Reproduce bounded E167 -> E117 structural searches and verify saved witnesses.

A finite structural witness needs equal full automorphism groups. Pynauty
computes source/target groups; the search encodes source invariance and blocks
extra target automorphisms until equality is achieved. These are exploratory
finite instances, not a proof of the global structural arrow. Every solve is
limited to five seconds, with at most forty symmetry exclusions per source.
"""
from pathlib import Path
from itertools import product,combinations
from collections import deque
import json,sys,time,threading
import pynauty
from pysat.solvers import Solver
from sympy.combinatorics import Permutation,PermutationGroup
sys.path.insert(0,'scripts')
from definability_167_4405_probe import encoding
W=Path('.cache/e167-117/reproduce');W.mkdir(parents=True,exist_ok=True)
def automorphisms(f):
 n=len(f);N=n+4*n*n;adj={i:[] for i in range(N)}
 def edge(a,b):adj[a].append(b);adj[b].append(a)
 for x,y in product(range(n),repeat=2):
  b=n+4*(x*n+y)
  for k,z in enumerate((x,y,f[x][y])):edge(b,b+k+1);edge(b+k+1,z)
 colors=[set(range(n))]+[{n+4*i+k for i in range(n*n)} for k in range(4)]
 gs,size,exp,_,_=pynauty.autgrp(pynauty.Graph(N,False,adj,colors))
 gs=[g[:n] for g in gs]
 return gs,round(size*10**exp)
def source_data():
 ds=json.loads(Path('data/definability_167_117_probe.json').read_text())['models']
 for d in ds:yield d['label'],d['source']
def run(label,f):
 n=len(f);st=time.monotonic();gs,size=automorphisms(f);G=PermutationGroup([Permutation(g) for g in gs])
 assert G.order()==size
 t,m=encoding(n,gs);p=lambda x,y,z:t[(x*n+y)*n+z]
 cs=set()
 def add(xs):
  s=set(v for v in xs if v)
  if not any(-v in s for v in s):cs.add(tuple(sorted(s)))
 for x,y in product(range(n),repeat=2):
  vs=[p(x,y,z) for z in range(n) if p(x,y,z)];add(vs)
  for a,b in combinations(vs,2):add([-a,-b])
 for x,y,u,v in product(range(n),repeat=4):
  if p(x,y,u) and p(u,x,v):add([-p(x,y,u),-p(u,x,v),p(y,v,x)])
 for x,z in product(range(n),repeat=2):
  for y,u in combinations(range(n),2):
   if p(x,y,z) and p(x,u,z):add([-p(x,y,z),-p(x,u,z)])
 sol=Solver(name='minisat22',bootstrap_with=list(cs));nv=m;extras=[]
 print(label,n,'sourceAut',size,'vars',m,flush=True)
 for i in range(40):
  timer=threading.Timer(5,sol.interrupt);timer.start();sat=sol.solve_limited(expect_interrupt=True);timer.cancel();sol.clear_interrupt()
  if sat is None:status='TIMEOUT';break
  if not sat:status='UNSAT';break
  pos=set(sol.get_model());h=[[next(z for z in range(n) if p(x,y,z) in pos) for y in range(n)] for x in range(n)]
  assert all(h[y][h[h[x][y]][x]]==x for x,y in product(range(n),repeat=2))
  hg,hs=automorphisms(h)
  for g in hg:
   assert all(g[h[x][y]]==h[g[x]][g[y]] for x,y in product(range(n),repeat=2))
  print(' iteration',i,'targetAut',hs,'seconds',round(time.monotonic()-st,3),flush=True)
  if hs==size:
   status='MATCHED';break
  s=next(g for g in hg if not G.contains(Permutation(g)))
  pairs={tuple(sorted((p(x,y,z),p(s[x],s[y],s[z])))) for x,y,z in product(range(n),repeat=3)};w=[]
  for a,b in pairs:
   if a==b:continue
   if not a:w.append(b);continue
   if not b:w.append(a);continue
   nv+=1;q=nv
   for c in [[-q,a,b],[-q,-a,-b],[q,-a,b],[q,a,-b]]:sol.add_clause(c)
   w.append(q)
  sol.add_clause(w);extras.append(s)
 else:status='ITERATION_LIMIT'
 result=dict(label=label,order=n,status=status,source=f,source_generators=gs,source_aut_size=size,excluded_autos=extras,seconds=time.monotonic()-st)
 if status=='MATCHED':result.update(target=h,target_generators=hg,target_aut_size=hs)
 (W/(label+'.json')).write_text(json.dumps(result,indent=2));print(label,status,'seconds',round(time.monotonic()-st,3),flush=True)
 sol.delete()
def verify():
 rows=json.loads(Path('data/definability_167_117_probe.json').read_text())['models']
 for d in rows:
  n=d['order'];f=d['source'];h=d['target']
  assert all(f[f[y][x]][f[x][y]]==x for x,y in product(range(n),repeat=2))
  assert all(h[y][h[h[x][y]][x]]==x for x,y in product(range(n),repeat=2))
  fg,fs=automorphisms(f);hg,hs=automorphisms(h)
  assert fs==hs==d['source_aut_size']==d['target_aut_size']
  group=PermutationGroup([Permutation(g) for g in fg])
  assert all(group.contains(Permutation(g)) for g in hg)
 print('Verified',len(rows),'E167/E117 pairs with equal full automorphism groups.')
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--search',action='store_true')
 args=parser.parse_args()
 verify()
 if args.search:
  for label,f in source_data():run(label,f)

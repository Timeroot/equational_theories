#!/usr/bin/env python3
"""Replay the 507 saved offset spaces for the forty-operation E917 candidate.

This bounded research check is not a converse theorem. Run from the repository
root. Output is JSON on stdout, with progress on stderr. Requires NumPy.
"""
import sys,json,itertools
from pathlib import Path
from functools import lru_cache
import numpy as np
sys.path.insert(0,'scripts')
from check_parastrophe_e917_sandwich import rref,core,unit,H,F,G
sources=json.load(open('data/parastrophes/repository_image_models_20261103.json'))['sources']['917']['tables']
supplement=json.load(open('data/parastrophes/e917_unary_counterexamples_20261104.json'))
for D in [supplement['base']]+[r['division'] for r in supplement['extensions']]:
 sources.append([[row.index(j) for j in range(len(D))] for row in D])
# Validate the supplemental source data independently of the offset scan.
D=supplement['base']
for ext in supplement['extensions']:
 phi=ext['offset'];n=len(D)
 assert ext['division']==[[2*D[i//2][j//2]+(i%2+j%2+phi[i//2][j//2])%2
   for j in range(2*n)]for i in range(2*n)]
for D in [supplement['base']]+[r['division']for r in supplement['extensions']]:
 n=len(D);q=lambda x:D[D[x][D[x][x]]][x]
 assert all(sorted(row)==list(range(n))for row in D)
 assert all(D[x][q(x)]==x for x in range(n))
 assert all(D[y][D[q(x)][D[x][y]]]==x for x in range(n)for y in range(n))
 f=lambda x:D[q(x)][x]
 if n==8:
  assert q(f(0))!=q(0) and f(f(0))!=0
 elif D==supplement['extensions'][0]['division']:
  assert f(f(f(f(0))))!=0
 else:
  assert q(f(f(0)))!=q(0)
def operation_count(t):
 return 0 if isinstance(t,int) else 1+operation_count(t[0])+operation_count(t[1])
assert operation_count((((unit(unit(3)),(unit(2),1)),4),H(0,((3,(2,1)),4))))==40
reports=[]
for sn,source in enumerate(sources):
 n=len(source);base=[[row.index(j) for j in range(n)] for row in source]
 for prime in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]:
  for B in range(1,prime):
   P=B**11+B**10-B**9+2*B**5+1;Q=B**8+B**7-B**6-B**3+B**2-1
   if P%prime or Q%prime: continue
   A=-B**3%prime;zero=np.zeros(n*n,dtype=np.int64)
   @lru_cache(None)
   def val(t,x,y):
    if isinstance(t,int):return (x,y)[t],zero.copy()
    i,u=val(t[0],x,y);j,v=val(t[1],x,y)
    off=(A*u+B*v)%prime;off[i*n+j]+=1
    return base[i][j],off%prime
   us=[val(unit(0),x,x)[1] for x in range(n)]
   aa=[A*us[next(i for i in range(n) if base[i][0]==k)]%prime for k in range(n)]
   bb=[B*aa[base[0].index(k)]%prime for k in range(n)]
   cc=[A*(2*aa[i]+bb[i])%prime for k in range(n) for i in [next(i for i in range(n) if base[i][0]==k)]]
   cons=[]
   for x,y in itertools.product(range(n),repeat=2):
    k=base[x][y]
    cons.extend([(A*us[x]-aa[k])%prime,(B*aa[y]-bb[k])%prime,(A*(2*aa[x]+bb[x])-cc[k])%prime,(val(F(0,1),x,y)[1]+A*cc[y])%prime])
   mat,piv=rref(cons,prime);bad=None
   for x in range(n):
    residual=us[x].copy()
    for row,j in zip(mat,piv):residual=(residual-residual[j]*row)%prime
    if np.any(residual):
     k=int(np.nonzero(residual)[0][0]);off=np.zeros(n*n,dtype=np.int64);off[k]=1
     for row,j in zip(mat,piv):off[j]=-row[k]%prime
     assert np.all(np.array(cons).dot(off)%prime==0)
     bad={'source':source,'A':A,'B':B,'prime':prime,'offset':off.reshape(n,n).tolist(),'failure_input':x};break
   report={'seed':sn,'order':n,'prime':prime,'B':B,'rank':len(piv),'counterexample':bad}
   reports.append(report)
   if bad: print('COUNTEREXAMPLE',report,file=sys.stderr,flush=True)
 print('seed',sn,'spaces',len(reports),'bad',sum(r['counterexample'] is not None for r in reports),file=sys.stderr,flush=True)
saved=json.load(open('data/parastrophes/e917_power_comparison_20261104.json'))['offset_spaces']
assert reports==saved, 'The recomputed spaces differ from the saved research record.'
print(json.dumps({'spaces':len(reports),'counterexamples':sum(r['counterexample'] is not None for r in reports),'matches_saved_record':True},indent=2))

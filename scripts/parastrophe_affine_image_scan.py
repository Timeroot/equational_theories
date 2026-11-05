#!/usr/bin/env python3
"""Search affine countermodels to E872 division-image candidates.

D(x,y)=Ax+By+c on (Z/nZ)^d. The matrix family tests all A,B; the local
family takes A,B polynomial in one nilpotent Jordan block. Four symbolic
coefficients test every assignment, and kernels test every constant c.
Reported misses concern only this explicit bounded family.
"""
import argparse,json,time,itertools
from pathlib import Path
import numpy as np
from functools import lru_cache
from parastrophe_rewrite_replay import freeze
from parastrophe_e872_compression import core,BASE
# Each coefficient is a noncommutative polynomial, represented by words in A,B.
@lru_cache(None)
def coeff(t):
 if isinstance(t,int):
  if t not in (0,1,2):raise ValueError("Only three-variable terms are supported")
  return tuple({():1}if i==t else{} for i in range(4))
 u,v=map(coeff,t);out=[]
 for j,(a,b) in enumerate(zip(u,v)):
  d={(0,)+w:c for w,c in a.items()}
  for w,c in b.items():d[(1,)+w]=d.get((1,)+w,0)+c
  if j==3:d[()]=d.get((),0)+1
  out.append(d)
 return tuple(out)

def scan(record,p,d,local=False,verbose=False,triangular=False):
 if p<2 or not 1<=d<=3:raise ValueError("Expected modulus >=2 and dimension 1..3")
 if local and triangular:raise ValueError("Choose only one matrix family")
 cs=record["rewrite_replay"]["unresolved"]
 I=np.eye(d,dtype=np.int64)
 if local:
  J=np.diag(np.ones(d-1,dtype=np.int64),1);ps=[I]
  for i in range(1,d):ps.append(ps[-1]@J)
  mats=np.array([sum((c*m for c,m in zip(cs,ps)),np.zeros_like(I))%p for cs in itertools.product(range(p),repeat=d)])
 elif triangular:
  entries=[(i,j)for i in range(d)for j in range(i,d)];mats=[]
  for values in itertools.product(range(p),repeat=len(entries)):
   matrix=np.zeros((d,d),dtype=np.int64)
   for ij,value in zip(entries,values):matrix[ij]=value
   mats.append(matrix)
  mats=np.array(mats)
 else:mats=np.array(list(itertools.product(range(p),repeat=d*d))).reshape(-1,d,d)
 size=len(mats);N=size*size
 vectors=np.array(list(itertools.product(range(p),repeat=d)),dtype=np.int64).T
 polys=[coeff(freeze(c['term']))for c in cs];u=coeff((0,core(0)));t=coeff(BASE)
 found={};st=time.time()
 for off in range(0,N,2048):
  ids=np.arange(off,min(off+2048,N));A=mats[ids//size];B=mats[ids%size]
  @lru_cache(None)
  def word(w):
   if not w:return np.broadcast_to(I,A.shape)
   return ((A if w[0]==0 else B)@word(w[1:]))%p
  @lru_cache(None)
  def ev(poly):
   ans=np.zeros_like(A)
   for w,c in poly:ans=(ans+c*word(w))%p
   return ans
  def e(poly):return ev(tuple(sorted(poly.items())))
  good=np.all(e(u[0])==I,axis=(1,2))&np.all(e(t[0])==I,axis=(1,2))&np.all(e(t[1])==0,axis=(1,2))
  # Try zero offset first, then all offsets in the constant coefficient's kernel.
  for c,poly in zip(cs,polys):
   if c['index']in found:continue
   valid=np.ones(len(ids),dtype=bool)
   for j,co in enumerate(poly[:3]):
    valid&=np.all(e(co)==(I if j==0 else 0),axis=(1,2))
    if not np.any(valid):break
   hit=np.flatnonzero(valid & ~good)
   offset=np.zeros(d,dtype=np.int64)
   if not len(hit) and np.any(valid):
    possible=np.flatnonzero(valid)
    constant=e(poly[3])[possible]@vectors%p
    allowed=np.all(constant==0,axis=1)
    wrong=np.any(e(u[3])[possible]@vectors%p!=0,axis=1)|np.any(e(t[3])[possible]@vectors%p!=0,axis=1)
    hits=np.argwhere(allowed&wrong)
    if len(hits):
     row,col=hits[0];hit=[possible[row]];offset=vectors[:,col]
   if len(hit):
    k=int(hit[0]);found[c['index']]={'index':c['index'],'A':A[k].tolist(),'B':B[k].tolist(),'offset':offset.tolist()}
    if verbose:print('hit',p,d,found[c['index']],flush=True)
  word.cache_clear();ev.cache_clear()
  if verbose and off%32768==0:print('progress',p,d,off,N,len(found),flush=True)
 out={'p':p,'dimension':d,'coefficient_pairs':N,'offset':'all vectors', 'family':'truncated polynomial ring' if local else 'upper triangular matrices' if triangular else 'all matrices','hits':list(found.values()),'seconds':time.time()-st}
 return out

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument("record",type=Path)
 parser.add_argument("--modulus",type=int,required=True)
 parser.add_argument("--dimension",type=int,default=2)
 parser.add_argument("--family",choices=["matrices","local","triangular"],default="matrices")
 parser.add_argument("--output",type=Path,required=True)
 args=parser.parse_args()
 result=scan(json.loads(args.record.read_text()),args.modulus,args.dimension,args.family=="local",True,triangular=args.family=="triangular")
 args.output.write_text(json.dumps(result,indent=2)+"\n")
 print(f"{result['coefficient_pairs']} coefficient pairs; {len(result['hits'])} candidate refutations.")

if __name__ == "__main__":main()

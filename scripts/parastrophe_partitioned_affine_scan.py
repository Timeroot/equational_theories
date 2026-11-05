#!/usr/bin/env python3
"""Search two-part affine countermodels to E872 image candidates.

The quotient is either right projection or XOR on two elements. Each of its
four ordered pairs has an independent fibre operation P*u+B*v+C over F_p,
with B nonzero. Variable coefficients filter P,B; finite-field nullspaces test
all four constants C without enumerating their p^4 possible assignments.
Every positive witness is independently checked as a multiplication table.
"""
import argparse,json,itertools,time
from pathlib import Path
from functools import lru_cache
import numpy as np
from parastrophe_e872_compression import Model,core,BASE
from parastrophe_rewrite_replay import freeze
def nullspace(rows,p):
 rows=[list(map(lambda x:int(x)%p,r))for r in rows if np.any(r)];rank=0;piv=[]
 for col in range(4):
  pivot=next((i for i in range(rank,len(rows))if rows[i][col]),None)
  if pivot is None:continue
  rows[rank],rows[pivot]=rows[pivot],rows[rank]
  fac=pow(rows[rank][col],-1,p);rows[rank]=[(v*fac)%p for v in rows[rank]]
  for i in range(len(rows)):
   if i!=rank and rows[i][col]:
    fac=rows[i][col];rows[i]=[(a-fac*b)%p for a,b in zip(rows[i],rows[rank])]
  piv.append(col);rank+=1
  if rank==4:break
 for f in set(range(4))-set(piv):
  v=[0]*4;v[f]=1
  for i,k in enumerate(piv):v[k]=-rows[i][f]%p
  yield v

def scan(record,p,kind,selected=None,verbose=False):
 if p<2 or any(p%d==0 for d in range(2,int(p**0.5)+1)):
  raise ValueError("The fibre modulus must be prime")
 if kind not in ("projection","xor"):raise ValueError("Unknown quotient")
 cs=[c for c in record["rewrite_replay"]["unresolved"] if selected is None or c["index"]in selected]
 if not cs:raise ValueError("No selected candidates")
 N=(p*(p-1))**4;st=time.time();found={};variables_survived={c['index']:0 for c in cs}
 Q=[[0,1],[0,1]]if kind=='projection'else[[0,1],[1,0]]
 terms=[freeze(c['term'])for c in cs]
 for off in range(0,N,2048):
  ids=np.arange(off,min(off+2048,N));digits=np.array(np.unravel_index(ids,(p*(p-1),)*4)).T
  P=digits//(p-1);B=digits%(p-1)+1;n=len(ids)
  valid=np.ones((len(cs),n),dtype=bool);good=np.ones(n,dtype=bool)
  constants=[[]for c in cs];basis=[]
  for xyz in itertools.product(range(2),repeat=3):
   @lru_cache(None)
   def ev(t):
    if isinstance(t,int):
     a=np.zeros((7,n),dtype=np.int16);a[t,:]=1;return xyz[t],a
    a,u=ev(t[0]);b,v=ev(t[1]);cell=2*a+b
    z=(P[:,cell]*u+B[:,cell]*v)%p;z[3+cell]=(z[3+cell]+1)%p
    return Q[a][b],z
   for bt in [(0,core(0)),BASE]:
    colour,z=ev(bt);good&=(colour==xyz[0])&np.all(z[:3]==np.array([1,0,0])[:,None],axis=0);basis.append(z[3:])
   for j,t in enumerate(terms):
    if cs[j]['index']in found:continue
    colour,z=ev(t);valid[j]&=(colour==xyz[0])&np.all(z[:3]==np.array([1,0,0])[:,None],axis=0);constants[j].append(z[3:])
   ev.cache_clear()
  for j,c in enumerate(cs):
   i=c['index']
   if i in found:continue
   possibilities=np.flatnonzero(valid[j]);variables_survived[i]+=len(possibilities)
   for k in possibilities:
    C=[0]*4
    if good[k]:
     mat=np.stack([z[:,k]for z in constants[j]]);base=np.stack([z[:,k]for z in basis])
     C=next((v for v in nullspace(mat,p)if np.any(base@v%p)),None)
     if C is None:continue
    def op(x,y):
     a,u=divmod(x,p);b,v=divmod(y,p);cell=2*a+b
     return p*Q[a][b]+int((P[k,cell]*u+B[k,cell]*v+C[cell])%p)
    table=[[op(x,y)for y in range(2*p)]for x in range(2*p)];M=Model(table)
    assert M.holds(terms[j]) and not M.is_image()
    found[i]={'index':i,'P':P[k].tolist(),'B':B[k].tolist(),'C':list(map(int,C)),'model':table}
    if verbose:print('HIT',p,kind,i,flush=True)
    break
  if verbose and off%32768==0:print('progress',p,kind,off,N,len(found),flush=True)
  if len(found)==len(cs):break
 out={'p':p,'quotient':Q,'coefficient_choices_total':N,'choices_checked':min(off+2048,N),'offsets':'all four independent constants, via nullspaces','candidates':[c['index']for c in cs],'variable_solutions':variables_survived,'hits':list(found.values()),'seconds':time.time()-st}
 return out

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument("record",type=Path)
 parser.add_argument("--prime",type=int,required=True)
 parser.add_argument("--quotient",choices=["projection","xor"],required=True)
 parser.add_argument("--candidate",type=int,action="append")
 parser.add_argument("--output",type=Path,required=True)
 args=parser.parse_args()
 result=scan(json.loads(args.record.read_text()),args.prime,args.quotient,args.candidate,True)
 args.output.write_text(json.dumps(result,indent=2)+"\n")
 print(f"{result['choices_checked']} coefficient choices checked; {len(result['hits'])} candidates refuted.")

if __name__=="__main__":main()

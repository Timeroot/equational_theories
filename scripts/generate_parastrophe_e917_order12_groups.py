#!/usr/bin/env python3
"""External research normal forms for E917 candidate counterexamples of order 12.

A free output group has order dividing 12. Enumerate generating pairs in the
known groups of those orders, up to their rooted regular-action presentations.
--v4-units further enumerates the 120 possible unit involutions for the sole
Klein-four output pair, modulo its 384 centralizing relabelings. The group
classification and these enumerations are not Lean certificates.
"""
import argparse
import itertools
import json
from pathlib import Path

def groups():
 for n in [2,3,4,6,12]:yield 'C'+str(n),list(range(n)),lambda x,y,n=n:(x+y)%n
 for m,n in [(2,2),(6,2)]:
  elems=list(itertools.product(range(m),range(n)))
  yield 'C'+str(m)+'xC'+str(n),elems,lambda x,y,m=m,n=n:((x[0]+y[0])%m,(x[1]+y[1])%n)
 for n in [3,6]:
  elems=list(itertools.product(range(n),range(2)))
  yield 'D'+str(2*n),elems,lambda x,y,n=n:((x[0]+(-1 if x[1] else 1)*y[0])%n,x[1]^y[1])
 elems=list(itertools.product(range(6),range(2)))
 yield 'Dic12',elems,lambda x,y:((x[0]+(-1 if x[1] else 1)*y[0]+3*x[1]*y[1])%6,x[1]^y[1])
 elems=[p for p in itertools.permutations(range(4))if sum(p[i]>p[j]for i in range(4)for j in range(i+1,4))%2==0]
 yield 'A4',elems,lambda x,y:tuple(x[y[i]]for i in range(4))

def cases(N):
 seen=set()
 for name,elems,mul in groups():
  assert N%len(elems)==0
  one=elems[0];assert all(mul(one,x)==x and mul(x,one)==x for x in elems)
  assert all(mul(mul(x,y),z)==mul(x,mul(y,z))for x in elems for y in elems for z in elems)
  for a,b in itertools.permutations(elems[1:],2):
   order=1;t=b
   while t!=one:t=mul(b,t);order+=1
   if (N//order*(order-1))%2:continue
   visit=[one];inds={one:0}
   for x in visit:
    for g in [a,b]:
     v=mul(g,x)
     if v not in inds:inds[v]=len(visit);visit.append(v)
   if len(visit)!=len(elems):continue
   aa=tuple(inds[mul(a,x)]for x in visit);bb=tuple(inds[mul(b,x)]for x in visit)
   if (aa,bb)in seen:continue
   seen.add((aa,bb));m=len(elems)
   yield name,[m*(x//m)+aa[x%m]for x in range(N)],[m*(x//m)+bb[x%m]for x in range(N)]

def v4_units():
 name,a,b=next((name,a,b)for name,a,b in cases(12)if name=='C2xC2')
 n=12;mul=lambda p,q:tuple(p[q[x]]for x in range(n));inv=lambda p:tuple(p.index(x)for x in range(n))
 one=tuple(range(n));c=mul(a,b);H=[one,tuple(a),tuple(b),c]
 unseen=set(range(n));blocks=[]
 while unseen:
  x=min(unseen);block=sorted({g[x]for g in H});blocks.append(block);unseen-=set(block)
 centr=[]
 for bp in itertools.permutations(range(3)):
  for targets in itertools.product(*[blocks[bp[i]]for i in range(3)]):
   p=[0]*n
   for i,block in enumerate(blocks):
    for g in H:p[g[block[0]]]=g[targets[i]]
   assert sorted(p)==list(range(n))
   assert all(p[g[x]]==g[p[x]]for g in[a,b]for x in range(n))
   centr.append(tuple(p))
 pairs=[];unseen=set(range(n))
 while unseen:
  x=min(unseen);pairs.append((x,c[x]));unseen-=set(pairs[-1])
 def matchings(inds):
  if not inds:yield [];return
  x=inds[0]
  for y in inds[1:]:
   for rest in matchings([i for i in inds if i not in[x,y]]):yield [(x,y)]+rest
 us=set()
 for matching in matchings(list(range(6))):
  for signs in itertools.product(range(2),repeat=3):
   u=[0]*n
   for (i,j),sign in zip(matching,signs):
    for k in range(2):u[pairs[i][k]]=pairs[j][k^sign];u[pairs[j][k^sign]]=pairs[i][k]
   assert mul(u,u)==one and mul(u,c)==mul(c,u)
   assert all(u[x]!=x and u[x]!=c[x]for x in range(n))
   us.add(tuple(u))
 reps={min(mul(mul(p,u),inv(p))for p in centr)for u in us}
 assert len(centr)==384 and len(us)==120 and len(reps)==10
 return [{'case':i,'group':'V4 with fixed unit','a':a,'b':b,'fixed_unit':list(u)}for i,u in enumerate(sorted(reps))]

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--v4-units',action='store_true')
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 rows=v4_units()if args.v4_units else [{'case':i,'group':name,'a':a,'b':b}for i,(name,a,b)in enumerate(cases(12))]
 assert len(rows)==(10 if args.v4_units else 35)
 args.output.write_text(json.dumps(rows,indent=2)+'\n')
 print(len(rows),'normal forms')

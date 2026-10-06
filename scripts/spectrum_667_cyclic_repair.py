#!/usr/bin/env python3
"""Try exact replacement of one or two blocks in a near difference family.

A positive output is a full certificate. Failure only concerns replacements
of the selected frozen near-family, not all designs or all magmas.
"""
import argparse,itertools,json,time

def distances(row,n):
 return [min(abs(a-b),n-abs(a-b)) for i,a in enumerate(row) for b in row[:i]]

def canonical(row,n):
 return min(tuple(sorted((sgn*(x-a))%n for x in row)) for a in row for sgn in [1,-1])

def cliques(n,k,allowed,end,first=False):
 V=sorted({x for d in allowed for x in (d,n-d)});adj=[]
 for a in V:adj.append(sum(1<<j for j,b in enumerate(V) if a!=b and min(abs(a-b),n-abs(a-b)) in allowed))
 def rec(xs,cands,seen):
  if time.monotonic()>end:raise TimeoutError
  if len(xs)==k:
   if tuple(xs)==canonical(xs,n):yield xs,seen
   return
  if cands.bit_count()<k-len(xs):return
  while cands:
   bit=cands&-cands;j=bit.bit_length()-1;cands-=bit;a=V[j];nd=0;ok=True
   for b in xs:
    d=min(abs(a-b),n-abs(a-b));db=1<<d
    if seen&db or nd&db:ok=False;break
    nd|=db
   if ok:yield from rec(xs+[a],cands&adj[j],seen|nd)
 yield from rec([0],(1<<len(V))-1,0)

def repair(data,seconds):
 n=data['order'];blocks=data['best_blocks'];end=time.monotonic()+seconds;trials=[]
 for count in [1,2]:
  for free in itertools.combinations(range(len(blocks)),count):
   ds=[d for i,row in enumerate(blocks) if i not in free for d in distances(row,n)]
   if len(ds)!=len(set(ds)):continue
   allowed=set(range(1,(n+1)//2))-set(ds);free=sorted(free,key=lambda i:len(blocks[i]));tested=0
   try:
    for row,seen in cliques(n,len(blocks[free[0]]),allowed,end):
     tested+=1
     if count==1:chosen=[row]
     else:
      remain={d for d in allowed if not (seen>>d)&1}
      second=next(cliques(n,len(blocks[free[1]]),remain,end),None)
      if second is None:continue
      chosen=[row,second[0]]
     answer=[list(row) for row in blocks]
     for i,row in zip(free,chosen):answer[i]=row
     assert sorted(d for row in answer for d in distances(row,n))==list(range(1,(n+1)//2))
     return {'order':n,'status':'FOUND','blocks':answer,'free_blocks':free,'tested':tested}
   except TimeoutError:return {'order':n,'status':'UNKNOWN','trials':trials,'timeout_free':free,'tested':tested}
   trials.append({'free':free,'first_candidates':tested,'status':'no repair'})
 return {'order':n,'status':'NO_ONE_OR_TWO_BLOCK_REPAIR','trials':trials}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('input');p.add_argument('--seconds',type=int,default=60);p.add_argument('--output');a=p.parse_args();out=repair(json.load(open(a.input)),a.seconds);txt=json.dumps(out,indent=2)+'\n'
 if a.output:open(a.output,'w').write(txt)
 print(txt)

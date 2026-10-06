#!/usr/bin/env python3
"""Bounded CP-SAT search for cyclic mixed-size difference families.

Only positive certificates are used as spectrum evidence. UNSAT here excludes
one cyclic design family, not arbitrary E667 models.
"""
import argparse,json
from pathlib import Path
from ortools.sat.python import cp_model

def shapes(n):
 return [[5]*a+[7]*b+[8]*c for a in range((n-1)//20+1) for b in range((n-1)//42+1) for c in range((n-1)//56+1) if 10*a+21*b+28*c==(n-1)//2]

def solve(n,shape,anchor,seconds,seed=1):
 sizes=shapes(n)[shape];model=cp_model.CpModel();blocks=[];distances=[]
 for bi,k in enumerate(sizes):
  xs=[model.NewIntVar(0,n-1,f'x{bi}_{i}') for i in range(k)];model.Add(xs[0]==0)
  for i in range(k-1):model.Add(xs[i]<xs[i+1]);model.Add(xs[1]<=xs[i+1]-xs[i])
  model.Add(xs[1]<=n-xs[-1])
  if k==anchor and not any(sizes[bj]==anchor for bj in range(bi)):model.Add(xs[1]==1)
  for i in range(k):
   for j in range(i):
    d=model.NewIntVar(1,(n-1)//2,f'd{bi}_{i}_{j}');model.AddMinEquality(d,[xs[i]-xs[j],n-xs[i]+xs[j]]);distances.append(d)
  for bj in range(bi):
   if sizes[bj]==k:model.Add(blocks[bj][1]<=xs[1])
  blocks.append(xs)
 model.AddAllDifferent(distances)
 solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=seconds;solver.parameters.num_search_workers=2;solver.parameters.random_seed=seed
 status=solver.Solve(model)
 out={'order':n,'shape':shape,'anchor':anchor,'seconds':seconds,'seed':seed,'status':solver.StatusName(status),'branches':solver.NumBranches(),'conflicts':solver.NumConflicts()}
 if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
  bs=[[solver.Value(x) for x in xs] for xs in blocks];ds=[min(abs(a-b),n-abs(a-b)) for row in bs for i,a in enumerate(row) for b in row[:i]]
  assert sorted(ds)==list(range(1,(n+1)//2));out['blocks']=bs
 return out

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('order',type=int);p.add_argument('--shape',type=int,default=0);p.add_argument('--anchor',type=int,choices=[5,7,8],default=5);p.add_argument('--seconds',type=int,default=60);p.add_argument('--seed',type=int,default=1);p.add_argument('--output',type=Path);a=p.parse_args()
 out=solve(a.order,a.shape,a.anchor,a.seconds,a.seed);text=json.dumps(out,indent=2)+'\n'
 if a.output:a.output.write_text(text)
 print(text)

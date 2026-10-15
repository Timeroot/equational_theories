#!/usr/bin/env python3
"""Bounded searches for source laws admitting the eight-point Klein-four action.

The default five sources were tested for reuse of the already formalized
E4405 exclusion. Only positives are useful here; external UNSAT results are
research data. Every positive is independently checked against equations.txt.
"""
from pathlib import Path
import sys,json,time
from itertools import product
import z3
sys.path.insert(0,'scripts')
from spectrum_generate import load_equations,variables,satisfies
W=Path('.cache/klein-four-eight');W.mkdir(parents=True,exist_ok=True)
n=8;G=[[x^v for x in range(n)] for v in range(4)];eqs=load_equations()
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--laws',nargs='+',type=int,default=[1483,1486,3342,3545,4443])
args=parser.parse_args()
for law in args.laws:
 ctx=z3.Context();A,elts=z3.EnumSort('A',[f'e{i}' for i in range(n)],ctx=ctx);f=z3.Function('f',A,A,A);s=z3.Solver(ctx=ctx);s.set(timeout=20000)
 def ev(t,vals):return vals[t] if isinstance(t,str) else f(ev(t[0],vals),ev(t[1],vals))
 lhs,rhs=eqs[law-1];vs=sorted(variables(lhs)|variables(rhs))
 for values in product(range(n),repeat=len(vs)):
  if values[0] not in [0,4]:continue
  vals={x:elts[v] for x,v in zip(vs,values)};s.add(ev(lhs,vals)==ev(rhs,vals))
 for g in G[1:]:
  gf=z3.Function('g'+str(g[0]),A,A)
  s.add([gf(elts[x])==elts[g[x]] for x in range(n)])
  s.add([gf(f(elts[x],elts[y]))==f(elts[g[x]],elts[g[y]]) for x,y in product(range(n),repeat=2)])
 st=time.monotonic();status=s.check();d=dict(law=law,status=str(status),seconds=time.monotonic()-st)
 if status==z3.sat:
  model=s.model();indices={str(e):i for i,e in enumerate(elts)}
  table=[[indices[str(model.eval(f(x,y)))] for y in elts] for x in elts]
  assert satisfies(lhs,rhs,sum(table,[]),n)
  assert all(g[table[x][y]]==table[g[x]][g[y]] for g in G for x,y in product(range(n),repeat=2))
  d['model']=table
 (W/f'{law}.json').write_text(json.dumps(d,indent=2));print(law,status,round(d['seconds'],3),flush=True)

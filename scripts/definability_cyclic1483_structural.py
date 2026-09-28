#!/usr/bin/env python3
"""Replay the C3-equivariant E1485 structural obstruction search.

Writes a separate replay record to /tmp; does not change saved evidence.
Requires z3-solver. Every reported model and automorphism group is checked
by direct finite enumeration. The external UNSAT result is not a Lean proof.
"""
import z3,json,time,itertools,pathlib
n=8
rot=lambda x:((x<<1)&7)|(x>>2)
rot2=lambda x:rot(rot(x))
source=[[7^(rot(x)&rot2(y)) for y in range(n)] for x in range(n)]
cyclic={tuple(range(n)),tuple(map(rot,range(n))),tuple(map(rot2,range(n)))}
def auts(table):
 return [p for p in itertools.permutations(range(n)) if all(p[table[x][y]]==table[p[x]][p[y]] for x in range(n) for y in range(n))]
def check(table):
 return all(table[table[y][x]][table[x][table[z][y]]]==x for x,y,z in itertools.product(range(n),repeat=3))
start=time.monotonic();aa=auts(source);assert set(aa)==cyclic
report={'source':source,'source_automorphisms':aa,'rounds':[],'cuts':[],'status':'running'}
out=pathlib.Path('/tmp/cyclic8_structural_replay.json')
def save():out.write_text(json.dumps(report,indent=2))
print('source automorphisms',len(aa),flush=True)
op=z3.Function('op',z3.IntSort(),z3.IntSort(),z3.IntSort());s=z3.Solver()
for x in range(n):
 for y in range(n):
  s.add(op(x,y)>=0,op(x,y)<n)
  s.add(op(rot(x),rot(y))==z3.Sum([z3.If(op(x,y)==k,rot(k),0) for k in range(n)]))
  for z in range(n):s.add(op(op(y,x),op(x,op(z,y)))==x)
cutset=set()
def cut(p):
 if p in cutset:return
 assert p not in cyclic
 cutset.add(p);report['cuts'].append(p)
 s.add(z3.Or([op(p[x],p[y])!=z3.Sum([z3.If(op(x,y)==k,p[k],0) for k in range(n)]) for x in range(n) for y in range(n)]))
evidence=pathlib.Path(__file__).resolve().parent.parent/'data/spectrum/1483_cyclic8_structural_search.json'
seed=json.loads(evidence.read_text())['seed_table'];assert check(seed)
report['seed_table']=seed
seedauts=auts(seed);report['seed_automorphisms']=seedauts
for p in seedauts:
 if p not in cyclic:cut(p)
for iteration in range(30):
 left=300-(time.monotonic()-start)
 if left<=0:report['status']='total_timeout';break
 s.set(timeout=int(min(90,left)*1000))
 t=time.monotonic();res=s.check();elapsed=time.monotonic()-t
 print('round',iteration,res,'seconds',elapsed,'cuts',len(cutset),flush=True)
 rr={'round':iteration,'solver_result':str(res),'solver_seconds':elapsed,'cuts_before':len(cutset)};report['rounds'].append(rr)
 if res==z3.unsat:report['status']='unsat';save();break
 if res==z3.unknown:
  rr['reason']=s.reason_unknown();save()
  if left<=91:report['status']='unknown';break
  continue
 m=s.model();table=[[m.eval(op(x,y)).as_long() for y in range(n)] for x in range(n)]
 assert check(table)
 automorphisms=auts(table);assert cyclic.issubset(set(automorphisms))
 print('automorphisms',len(automorphisms),flush=True)
 rr['table']=table;rr['automorphisms']=automorphisms
 if set(automorphisms)==cyclic:report['status']='exact_C3_target';save();break
 for p in automorphisms:
  if p not in cyclic:cut(p)
 save()
else:report['status']='iteration_limit'
report['elapsed_seconds']=time.monotonic()-start;save()
print('final',report['status'],flush=True)

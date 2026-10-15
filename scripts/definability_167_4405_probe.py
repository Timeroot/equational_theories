#!/usr/bin/env python3
"""Bounded Aut-equivariant searches for the open finite FO arrow E167 -> E4405.

Tests the existing small permutation-action catalogue and a few cyclic actions.
Each CaDiCaL call has a three-second limit; no proof trace is generated. Positive
models are independently checked against the law and all action generators.
UNSAT and timeout results are exploratory, not Lean certificates.

The table variables are orbits of triples. An orbit assigning two outputs to
one input pair is forbidden; remaining orbits describe every equivariant binary
operation. Auxiliary target variables describe the common value in E4405.
"""
from pathlib import Path
from itertools import product,combinations,permutations
from concurrent.futures import ThreadPoolExecutor
import json,time,subprocess,hashlib
W=Path('.cache/e167-4405/orbits');W.mkdir(exist_ok=True)
def encoding(n,gens):
 roots=list(range(n**3))
 def find(a):
  while roots[a]!=a:roots[a]=roots[roots[a]];a=roots[a]
  return a
 def union(a,b):
  a,b=find(a),find(b)
  if a!=b:roots[max(a,b)]=min(a,b)
 idx=lambda x,y,z:(x*n+y)*n+z
 for g in gens:
  for x,y,z in product(range(n),repeat=3):union(idx(x,y,z),idx(g[x],g[y],g[z]))
 bad=set();seen=set()
 for x,y,z in product(range(n),repeat=3):
  a=find(idx(x,y,z));key=(x,y,a)
  if key in seen:bad.add(a)
  seen.add(key)
 ids={};table=[]
 for x,y,z in product(range(n),repeat=3):
  a=find(idx(x,y,z))
  if a in bad:table.append(0)
  else:
   if a not in ids:ids[a]=len(ids)+1
   table.append(ids[a])
 return table,len(ids)
def cnf(n,table,m,law):
 p=lambda x,y,z:table[(x*n+y)*n+z];cs=set()
 def add(xs):
  s=set(v for v in xs if v)
  if not any(-v in s for v in s):cs.add(tuple(sorted(s)))
 for x,y in product(range(n),repeat=2):
  vs=[p(x,y,z) for z in range(n) if p(x,y,z)]
  for delta in ([0,m] if law==4405 else [0]):
   add([v+delta for v in vs])
   for a,b in combinations(vs,2):add([-a-delta,-b-delta])
 if law==167:
  for x in range(n):add([p(x,x,x)])
  for x,y,u,v in product(range(n),repeat=4):
   a,b=p(y,x,u),p(x,y,v)
   if a and b:add([-a,-b,p(u,v,x)])
 else:
  for x,y,u,z in product(range(n),repeat=4):
   q=p(x,y,z);q=q+m if q else 0
   a,b=p(x,y,u),p(x,u,z)
   if a and b:add([-a,-b,q])
   a,b=p(y,x,u),p(u,x,z)
   if a and b:add([-a,-b,q])
 return sorted(cs)
def solve(label,n,gens,table,m,law):
 cs=cnf(n,table,m,law);path=W/f'{label}-{law}.cnf'
 path.write_text(f'p cnf {m*(2 if law==4405 else 1)} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
 start=time.monotonic()
 r=subprocess.run(['cadical','--seed=1','-t','3',str(path)],capture_output=True,text=True,timeout=5)
 out=dict(law=law,result={10:'SAT',20:'UNSAT'}.get(r.returncode,'TIMEOUT'),seconds=round(time.monotonic()-start,3),variables=m,clauses=len(cs))
 if r.returncode==10:
  positive={int(v) for l in r.stdout.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
  f=[[next(z for z in range(n) if table[(x*n+y)*n+z] in positive) for y in range(n)] for x in range(n)]
  assert all(g[f[x][y]]==f[g[x]][g[y]] for g in gens for x,y in product(range(n),repeat=2))
  assert all((f[f[y][x]][f[x][y]]==x if law==167 else f[x][f[x][y]]==f[f[y][x]][x]) for x,y in product(range(n),repeat=2))
  out['model']=f
 (W/f'{label}-{law}.json').write_text(json.dumps(out,indent=2)+'\n')
 return out
def run(item):
 label,n,gens,table,m=item
 source=solve(label,n,gens,table,m,167)
 result=dict(label=label,order=n,generators=gens,source=source)
 if source['result']=='SAT':result['target']=solve(label,n,gens,table,m,4405)
 (W/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(label,n,source['result'],result.get('target',{}).get('result'),flush=True)
 return result
def four_point_check():
 sources=[];targets=[];perms=list(permutations(range(4)))
 for values in product(range(4),repeat=8):
  f=[[values[4*(x//2)+(y^(x%2))]^(x%2) for y in range(4)] for x in range(4)]
  if all(f[f[y][x]][f[x][y]]==x for x,y in product(range(4),repeat=2)):sources.append(f)
  if all(f[x][f[x][y]]==f[f[y][x]][x] for x,y in product(range(4),repeat=2)):targets.append(f)
 auto=lambda f,p:all(p[f[x][y]]==f[p[x]][p[y]] for x,y in product(range(4),repeat=2))
 sizes=[];counts=[]
 for f in sources:
  autos=[p for p in perms if auto(f,p)];sizes.append(len(autos))
  counts.append(sum(all(auto(t,p) for p in autos) for t in targets))
 return dict(source_count=len(sources),target_count=len(targets),
             automorphism_group_orders=sorted(set(sizes)),
             compatible_target_counts=sorted(set(counts)),targets=targets)

if __name__=='__main__':
 actions=[]
 for p in Path('data').glob('definability_orbit_*.json'):
  d=json.loads(p.read_text());n=d.get('order',0)
  if 1<n<=24 and n%4 in (0,1) and 'generators' in d:actions.append((p.stem.removeprefix('definability_orbit_'),n,d['generators']))
 for n in (4,8,12,16):
  for step in (2,4,n):actions.append((f'cyclic{step}-copies{n//step}',n,[[step*(x//step)+(x+1)%step for x in range(n)]]))
 selected=[];seen=set()
 for label,n,gens in actions:
  table,m=encoding(n,gens);key=(n,tuple(table))
  if key not in seen:seen.add(key);selected.append((label,n,gens,table,m))
 print('Actions',len(selected),flush=True)
 with ThreadPoolExecutor(max_workers=3) as pool:rs=list(pool.map(run,selected))
 (W/'summary.json').write_text(json.dumps(dict(actions=rs,four_point=four_point_check()),indent=2)+'\n')

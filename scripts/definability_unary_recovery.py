#!/usr/bin/env python3
"""Reproduce UnaryRecoveryBounds.lean using finite congruence closure.

Run from the repository root with --check (default) or --write. This is an
untrusted proof generator: every union carries an explicit equality, and Lean
checks all emitted deductions and standard-axiom guards. Reaching a search limit
is a failure to find a proof, never evidence of a negative mathematical result.
"""
import argparse
import itertools
import re
from pathlib import Path
from spectrum_generate import load_equations, variables

E = load_equations()
TARGET_SOURCES = {72: [646], 434: [646], 1687: [646], 3587: [646],
    3600: [646], 3715: [621, 626, 646], 3716: [646], 3718: [646],
    4397: [646], 4400: [646], 4402: [646], 4416: [646], 4434: [646],
    4437: [646], 4471: [646], 4490: [646], 4502: [646]}
OUTPUT = Path('equational_theories/Definability/UnaryRecoveryBounds.lean')
class Limit(Exception):pass
class Graph:
 def __init__(self):self.nodes=[None];self.parent=[0];self.edge={};self.raw={};self.proofs=[];self.steps=0
 def find(self,a):
  while self.parent[a]!=a:a=self.parent[a]
  return a
 def path(self,a):
  if self.parent[a]==a:return 'rfl'
  e='e'+str(self.edge[a]);rest=self.path(self.parent[a]);return e if rest=='rfl' else f'({e}.trans {rest})'
 def mk(self,a,b):
  if (a,b) in self.raw:return self.raw[a,b]
  if len(self.nodes)>=2500:raise Limit()
  i=len(self.nodes);self.nodes.append((a,b));self.parent.append(i);self.raw[a,b]=i;return i
 def evaluate(self,t,env):return env[t] if isinstance(t,str) else self.mk(self.evaluate(t[0],env),self.evaluate(t[1],env))
 def union(self,a,b,given):
  ra,rb=self.find(a),self.find(b)
  if ra==rb:return False
  pa,pb=self.path(a),self.path(b)
  expr=f'(({pa}).symm.trans (({given}).trans ({pb})))'
  if ra<rb:left,right=rb,ra;expr=f'({expr}).symm'
  else:left,right=ra,rb
  idx=len(self.proofs);self.proofs.append({'left':left,'right':right,'proof':expr});self.parent[left]=right;self.edge[left]=idx;return True
 def rebuild(self):
  while True:
   d={};changed=False
   for c,node in enumerate(self.nodes):
    if node is None:continue
    a,b=node;key=self.find(a),self.find(b)
    if key in d:
     f=d[key]
     if self.find(c)!=self.find(f):
      u,v=self.nodes[f];pa=f'(({self.path(a)}).trans ({self.path(u)}).symm)';pb=f'(({self.path(b)}).trans ({self.path(v)}).symm)'
      changed |= self.union(c,f,f'congrArg₂ M.op {pa} {pb}')
    else:d[key]=c
   if not changed:return d
 def roots(self):return [i for i in range(len(self.nodes)) if self.find(i)==i]
 def solve(self,law):
  lhs,rhs=E[law-1];vs=sorted(variables(lhs)|variables(rhs),key='xyzw'.index);self.mk(0,0)
  for epoch in range(35):
   d=self.rebuild();roots=self.roots()
   if len(roots)>10:raise Limit()
   for j,args in enumerate(itertools.product(roots,repeat=len(vs))):
    self.steps+=1
    if self.steps>12000:raise Limit()
    env=dict(zip(vs,args));a=self.evaluate(lhs,env);b=self.evaluate(rhs,env)
    self.union(a,b,'h '+' '.join('v'+str(i) for i in args))
    if j%12==0:self.rebuild()
   d=self.rebuild();rr=self.roots()
   missing=[(a,b) for a in rr for b in rr if (a,b) not in d]
   if not missing:
    # Every surviving class must have been included in the preceding law substitutions.
    if set(rr) <= {self.find(i) for i in roots}:
     table=[];equalities=[]
     for a in rr:
      row=[]
      for b in rr:
       node=d[a,b];u,v=self.nodes[node];r=self.find(node)
       expr=f'((congrArg₂ M.op ({self.path(u)}).symm ({self.path(v)}).symm).trans ({self.path(node)}))'
       row.append(rr.index(r));equalities.append(expr)
      table.append(row)
     return {'law':law,'size':len(rr),'roots':rr,'nodes':self.nodes,'proofs':self.proofs,'table':table,'equalities':equalities}
   else:self.mk(*missing[0])
  raise Limit()

def refs(expr,letter):return set(map(int,re.findall(r'\b'+letter+r'(\d+)\b',expr)))
def nodeclosure(r,ids):
 todo=list(ids);out=set(ids)
 while todo:
  n=todo.pop();node=r['nodes'][n]
  if node:
   for i in node:
    if i not in out:out.add(i);todo.append(i)
 return sorted(out)
def lets(r,ids,indent):return [indent+('let v0 : G := x' if i==0 else f'let v{i} := M.op v{r["nodes"][i][0]} v{r["nodes"][i][1]}') for i in ids]

def render():
 R = [Graph().solve(a) for a in sorted(TARGET_SOURCES)]
 chunks = []
 for r in R:
  a=r['law'];k=r['size'];sources=TARGET_SOURCES[a]
  if not sources:continue
  used=set();todo=set().union(*(refs(e,'e') for e in r['equalities']))
  while todo:
   i=todo.pop()
   if i in used:continue
   used.add(i);todo|=refs(r['proofs'][i]['proof'],'e')-used
  ids=set(r['roots'])
  for i in used:
   p=r['proofs'][i];ids|={p['left'],p['right']}|refs(p['proof'],'v')
  ids=nodeclosure(r,ids);basisids=nodeclosure(r,set(r['roots']));vec='!['+', '.join(f'v{i}' for i in r['roots'])+']';table='!['+', '.join('!['+', '.join(map(str,row))+']' for row in r['table'])+']'
  lines=['import equational_theories.Definability.SmallGeneratedWitnesses','open Law Law.MagmaLaw Magma.GenerationOrder RecoverySubmagmas','namespace UnaryRecoveryBounds','',f'def basis{a} {{G : Type}} (M : Magma G) (x : G) : Fin {k} → G :=']+lets(r,basisids,'  ')+['  '+vec,'',f'def products{a} : Fin {k} → Fin {k} → Fin {k} := {table}','',f'theorem table{a} {{G : Type}} (M : Magma G) (h : @Equation{a} G M) (x : G) :',f'    ∀ i j, M.op (basis{a} M x i) (basis{a} M x j) = basis{a} M x (products{a} i j) := by']
  lines+=lets(r,ids,'  ')
  for i in sorted(used):
   p=r['proofs'][i];lines.append(f'  have e{i} : v{p["left"]} = v{p["right"]} := {p["proof"]}')
  lines += ['  intro i j',f'  change M.op ({vec} i) ({vec} j) = {vec} (products{a} i j)','  fin_cases i <;> fin_cases j']
  lines += ['  · exact '+e for e in r['equalities']]
  lines += ['',f'theorem closed{a} {{G : Type}} (M : Magma G) (h : @Equation{a} G M) (x : G) :',f'    Closed M.op (Set.range (basis{a} M x)) := by','  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩',f'  exact ⟨products{a} i j, (table{a} M h x i j).symm⟩','']
  for source in sources:
   n={621:4,626:5,646:6}[source];name=f'Equation{a}_not_termStructuralFromFin_Equation{source}_oneGenerated'
   lines += [f'theorem {name} : ¬ Law{a}.TermStructuralFromFin Law{source} := by','  intro h',f'  obtain ⟨N,hN,_,hr⟩ := h SmallGeneratedWitnesses.source{source}',f'    ((@Law{source}.models_iff (Fin {n}) SmallGeneratedWitnesses.source{source}).mpr SmallGeneratedWitnesses.law{source})',f'  have hh := cardinal_le_of_closed_range SmallGeneratedWitnesses.generates{source} hr',f'    (basis{a} N 0) ⟨0,rfl⟩ (closed{a} N ((@Law{a}.models_iff (Fin {n}) N).mp hN) 0)','  norm_num at hh','',f"/-- info: 'UnaryRecoveryBounds.{name}' depends on axioms: [propext, Classical.choice, Quot.sound] -/",'#guard_msgs (whitespace := lax) in',f'#print axioms {name}','']
  lines+=['end UnaryRecoveryBounds',''];chunks.append('\n'.join(lines).split('namespace UnaryRecoveryBounds\n',1)[1].rsplit('end UnaryRecoveryBounds',1)[0].strip())
 return 'import equational_theories.Definability.SmallGeneratedWitnesses\n\n/-! Explicit multiplication tables for submagmas generated by one element.\n\nFor each target law, the displayed unary terms form a closed set of at most\nfour elements. The proofs are short equational deductions; no solver or\nexternal certificate is trusted. A larger monogenic source cannot be recovered\nby terms from such a companion. See `docs/definability_generation_discovery.md`.\n-/\n\nopen Law Law.MagmaLaw Magma.GenerationOrder RecoverySubmagmas\nnamespace UnaryRecoveryBounds\n'+'\n\n'+'\n\n'.join(chunks)+'\n\nend UnaryRecoveryBounds\n'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    output = render()
    if args.write:
        OUTPUT.write_text(output)
    elif OUTPUT.read_text() != output:
        raise SystemExit('Generated Lean differs; run with --write and rebuild.')
    print(f'{OUTPUT}: reproduced 17 unary bounds and 19 recovery obstructions')

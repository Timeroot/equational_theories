#!/usr/bin/env python3
"""Reproduce counts for complete families preserved by translations and a projection."""
import argparse
import itertools
import json
import math
from pathlib import Path
import numpy as np
from spectrum_generate import load_equations, variables
from definability_ring_counts_check import term
ROOT=Path(__file__).resolve().parents[1]
E=load_equations()

def render(d):
    ns=d['namespace']
    def group_type(moduli):
        return '('+' × '.join(f'ZMod {m}' for m in moduli)+')'
    s=f'''import equational_theories.Definability.ProjectionFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Complete projection-compatible families, with independently reproduced counts. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}
abbrev A := {group_type(d['base_moduli'])}
abbrev B := {group_type(d['kernel_moduli'])}
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.ProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionFamily.family_generators p (.inl a)

'''
    counts={e[key]:e[key+'_count'] for e in d['candidates'] for key in ['source','target']}
    for law,count in sorted(counts.items()):
        l,r=E[law-1];k=1+max('xyzuvw'.index(v) for v in variables(l)|variables(r))
        s+=f'''private def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r)}⟩
private theorem count{law} : Fintype.card {{p : Params // ZeroTest (model p) law{law}}} = {count} := by native_decide

'''
    s+=f'end Magma.{ns}\n\nopen Magma.{ns}\n\n'
    for e in d['candidates']:
        a,b=e['source'],e['target'];k=1+max('xyzuvw'.index(v) for t in E[b-1] for v in variables(t));name=f'Equation{b}_not_termStructuralFromFin_Equation{a}_{ns[0].lower()+ns[1:]}'
        s+=f'''theorem {name} : ¬ Law{b}.TermStructuralFromFin Law{a} := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionFamily.gen (A := A) (B := B))
    model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage
    Magma.ProjectionFamily.family_generators
    (fun p => ZeroTest (model p) law{a}) (fun p => ZeroTest (model p) law{b})
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat {k} i))
  · rw [count{a}, count{b}]
    decide

#print axioms {name}

'''
    for name,axioms in d.get('axioms',{}).items():
        s=s.replace('#print axioms '+name+'\n','/-- info: '+axioms+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+name+'\n')
    return s

def check(d):
    mods=d['base_moduli']+d['kernel_moduli'];n=math.prod(mods);a=math.prod(d['base_moduli']);b=math.prod(d['kernel_moduli']);assert n==d['order'];size=a**a*b**(n-a);assert size==d['family_count']
    radix=np.cumprod([1]+mods[:-1]);pts=(np.arange(n)[:,None]//radix)%np.array(mods);G=((pts[:,None,:]+pts[None,:,:])%np.array(mods))@radix;P=np.arange(n)%a
    assert np.array_equal(P[G],G[P[:,None],P[None,:]])
    codes=np.arange(size,dtype=np.int64);f=np.empty((size,n),dtype=np.uint16);divisor=1
    for x in range(a):f[:,x]=codes//divisor%a;divisor*=a
    for x in range(a,n):f[:,x]=f[:,P[x]]+a*(codes//divisor%b);divisor*=b
    assert divisor==size and np.array_equal(P[f],f[:,P])
    # These coordinates recover each parameter independently, proving no repeats.
    for x in range(a):assert np.all(f[:,x]<a)
    inv=np.array([next(y for y in range(n) if G[x,y]==0) for x in range(n)]);difference=G[inv[:,None],np.arange(n)[None,:]]
    class Tables:
        def __getitem__(self,key):
            i,x,y=key
            return G[x,f[i,difference[x,y]]]
    T=Tables()
    def models(law):
        l,r=E[law-1];names=sorted(variables(l)|variables(r));vals=np.array(list(itertools.product(range(n),repeat=len(names))),dtype=np.uint16).T;active=np.arange(size);pos=0
        while len(active) and pos<vals.shape[1]:
            width=min(32,max(1,2000000//len(active)));batch=vals[:,pos:pos+width];pos+=width;cache={v:batch[j][None,:] for j,v in enumerate(names)};ix=active[:,None]
            def ev(t):
                if t not in cache:cache[t]=T[ix,ev(t[0]),ev(t[1])]
                return cache[t]
            active=active[np.broadcast_to(ev(l)==ev(r),(len(active),batch.shape[1])).all(axis=1)]
        return len(active)
    counts={law:models(law) for law in sorted({e[key] for e in d['candidates'] for key in ['source','target']})}
    for e in d['candidates']:
        assert counts[e['source']]==e['source_count'] and counts[e['target']]==e['target_count']
    print(d['namespace'],size,'operations: full-assignment counts',counts,flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');parser.add_argument('--only');args=parser.parse_args()
    for path in sorted((ROOT/'data').glob('definability_projection_group_count*.json')):
        d=json.loads(path.read_text())
        if args.only and args.only not in d['namespace']:continue
        check(d);p=ROOT/'equational_theories/Definability/Generated'/f'{d["namespace"]}.lean';s=render(d)
        if args.write:p.write_text(s)
        else:assert p.read_text()==s

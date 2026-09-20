#!/usr/bin/env python3
"""Verify projection families restricted by scalar actions on both factors."""
import argparse,itertools,json,math
from pathlib import Path
import numpy as np
from definability_projection_kernel_counts_check import kernel_chart,render as kernel_render,E
from definability_projection_group_counts_check import render as group_render
from definability_orbit_certificates_check import matrix
from definability_counting_upgrades_check import model_indices
ROOT=Path(__file__).resolve().parents[1]

def render(d):
    ns=d['namespace'];a=d['base_modulus'];b=d['kernel_modulus'];us=d['base_scalars'];chart=d['base_chart'];m=len(chart['representatives']);gcount=len(d['base_functions'])
    head=kernel_render(d).split('abbrev Params :=')[0].replace('import equational_theories.Definability.ProjectionKernelCounting','import equational_theories.Definability.ProjectionBaseCounting')
    head+=f'''def baseScalarData : Array A := #[{', '.join(map(str,us))}]
def baseMaps (i : Fin {len(us)}) : A →+ A where
  toFun x := baseScalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def gData : Array (Array A) := {matrix(d['base_functions'])}
def gvalues (p : Fin {gcount}) (a : A) : A := (gData.getD p.val #[]).getD a.val 0
def baseRepresentativeData : Array A := #[{', '.join(map(str,chart['representatives']))}]
def baseRepresentative (i : Fin {m}) : A := baseRepresentativeData.getD i.val 0
def baseTransportData : Array (Fin {m} × Fin {len(us)}) := #[{', '.join(f'({i}, {j})' for i,j in chart['transport'])}]
def baseTransport (a : A) := baseTransportData.getD a.val (0, 0)
def hvalues (q : Fin {m} → K) (a : A) : K := q (baseTransport a).1

theorem base_transport : ∀ a, baseMaps (baseTransport a).2 (baseRepresentative (baseTransport a).1) = a := by native_decide
theorem base_representative : ∀ i, (baseTransport (baseRepresentative i)).1 = i := by native_decide
theorem base_orbit : ∀ j a, (baseTransport a).1 = (baseTransport (baseMaps j a)).1 := by native_decide
theorem g_injective : Function.Injective gvalues := by native_decide
theorem g_maps : ∀ p j a, baseMaps j (gvalues p a) = gvalues p (baseMaps j a) := by native_decide
theorem g_coverage : ∀ g : A → A, (∀ j a, baseMaps j (g a) = g (baseMaps j a)) → ∃ p, gvalues p = g := by native_decide
theorem h_maps : ∀ q j a, hvalues q a = hvalues q (baseMaps j a) := by
  intro q j a
  exact congrArg q (base_orbit j a)
theorem h_injective : Function.Injective hvalues := by
  intro p q hpq
  funext i
  have h := congrFun hpq (baseRepresentative i)
  simpa only [hvalues, base_representative] using h
theorem h_coverage : ∀ h : A → K, (∀ j a, h a = h (baseMaps j a)) → ∃ q, hvalues q = h := by
  intro h hh
  refine ⟨fun i => h (baseRepresentative i), ?_⟩
  funext a
  have he := hh (baseTransport a).2 (baseRepresentative (baseTransport a).1)
  simpa only [base_transport] using he

abbrev Params := Fin {gcount} × (Fin {m} → K)
@[implicit_reducible] def model (p : Params) : Magma (A × B) :=
  Magma.ProjectionBaseFamily.fam values gvalues hvalues p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionBaseFamily.family_generators maps values baseMaps gvalues hvalues
    value_zero value_maps g_maps h_maps p (.inl (.inl a))

'''
    old=group_render(dict(d,base_moduli=[a],kernel_moduli=[b]));tail=old[old.index('private def law'):]
    tail=tail.replace('Magma.ProjectionFamily.gen (A := A) (B := B)','Magma.ProjectionBaseFamily.gen maps baseMaps')
    tail=tail.replace('model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage\n    Magma.ProjectionFamily.family_generators','model (Magma.ProjectionBaseFamily.family_injective values gvalues hvalues value_injective g_injective h_injective)\n    (Magma.ProjectionBaseFamily.coverage maps values baseMaps gvalues hvalues value_injective value_coverage g_coverage h_coverage)\n    (Magma.ProjectionBaseFamily.family_generators maps values baseMaps gvalues hvalues value_zero value_maps g_maps h_maps)')
    return head+tail

def check(d):
    a,b=d['base_modulus'],d['kernel_modulus'];n=a*b;us=d['base_scalars'];gs=[list(g) for g in itertools.product(range(a),repeat=a) if all(g[u*x%a]==u*g[x]%a for u in us for x in range(a))];assert gs==d['base_functions']
    bc=kernel_chart(a,us);assert d['base_chart']=={k:v for k,v in bc.items() if k in ['representatives','transport']}
    kc=kernel_chart(b,d['kernel_scalars']);fs=kc['functions'];assert fs==d['kernel_functions'] and d['unary_chart']=={k:v for k,v in kc.items() if k!='functions'}
    m=len(bc['representatives']);size=len(gs)*len(fs)**m;assert d['family_count']==size and d['order']==n
    codes=np.arange(size);g=np.array(gs)[codes%len(gs)];div=len(gs);h=np.empty((size,m),dtype=np.uint16)
    for i in range(m):h[:,i]=codes//div%len(fs);div*=len(fs)
    ix=np.array([i for i,j in bc['transport']])[np.arange(n)%a];f=g[:,np.arange(n)%a]+a*np.array(fs)[h[:,ix],np.arange(n)//a]
    G=np.array([[(x%a+y%a)%a+a*((x//a+y//a)%b) for y in range(n)] for x in range(n)]);inv=np.array([next(y for y in range(n) if G[x,y]==0) for x in range(n)]);diff=G[inv[:,None],np.arange(n)[None,:]];T=G[np.arange(n)[None,:,None],f[:,diff]].astype(np.uint16)
    assert len({tuple(row) for row in f})==size
    for gen in [np.arange(n)%a]+[np.arange(n)%a+a*(u*(np.arange(n)//a)%b) for u in d['kernel_scalars']]+[(u*(np.arange(n)%a)%a)+a*(np.arange(n)//a) for u in us]:assert np.array_equal(gen[T],T[:,gen[:,None],gen[None,:]])
    counts={law:len(model_indices(E,T,law)) for law in sorted({e[key] for e in d['candidates'] for key in ['source','target']})}
    for e in d['candidates']:assert counts[e['source']]==e['source_count'] and counts[e['target']]==e['target_count']
    print(d['namespace'],'complete family',size,'full-assignment counts',counts,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--only');args=p.parse_args()
    for path in sorted((ROOT/'data').glob('definability_projection_base_count*.json')):
        d=json.loads(path.read_text())
        if args.only and args.only not in d['namespace']:continue
        check(d);s=render(d);target=ROOT/'equational_theories/Definability/Generated'/f'{d["namespace"]}.lean'
        if args.write:target.write_text(s)
        else:assert target.read_text()==s

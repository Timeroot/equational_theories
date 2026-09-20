#!/usr/bin/env python3
"""Reproduce complete translation/projection families with prescribed kernel maps."""
import argparse,itertools,json,math
from pathlib import Path
import numpy as np
from definability_counting_upgrades_check import model_indices
from definability_orbit_certificates_check import matrix
from definability_projection_group_counts_check import render as group_render
from spectrum_generate import load_equations
ROOT=Path(__file__).resolve().parents[1];E=load_equations()

def kernel_chart(b, units):
    assert 1 in units and len(set(units))==len(units)
    assert all(math.gcd(u,b)==1 and u*v%b in units for u in units for v in units)
    reps=[];choices=[];stabilizers=[];transport=[None]*b
    for x in range(b):
        if transport[x] is not None:continue
        i=len(reps);reps.append(x)
        fixed=[j for j,u in enumerate(units) if u*x%b==x]
        stabilizers.append(fixed)
        choices.append([y for y in range(b) if (x!=0 or y==0) and all(units[j]*y%b==y for j in fixed)])
        for j,u in enumerate(units):transport[u*x%b]=[i,j]
    rows=sorted([[(units[j]*values[i])%b for i,j in transport] for values in itertools.product(*choices)])
    width=max(map(len,stabilizers))
    return dict(representatives=reps,choices=choices,transport=transport,
                stabilizers=[s+[units.index(1)]*(width-len(s)) for s in stabilizers],functions=rows)

def render(d):
    ns=d['namespace'];a=d['base_modulus'];b=d['kernel_modulus'];units=d['kernel_scalars'];fs=d['kernel_functions'];k=len(fs)
    core=f'''import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}
abbrev A := ZMod {a}
abbrev B := ZMod {b}
abbrev K := Fin {k}
def scalarData : Array B := #[{', '.join(map(str,units))}]
def maps (i : Fin {len(units)}) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := {matrix(fs)}
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD x.val 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
theorem value_coverage : ∀ f : B → B, f 0 = 0 →
    (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f := by native_decide

abbrev Params := Magma.ProjectionKernelFamily.Params A K
@[implicit_reducible] def model (p : Params) : Magma (A × B) :=
  Magma.ProjectionKernelFamily.fam values p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps p (.inl a)

'''
    if d.get('unary_chart'):
        chart=d['unary_chart'];m=len(chart['representatives']);width=len(chart['stabilizers'][0])
        data=f'''def representativeData : Array B := #[{', '.join(map(str,chart['representatives']))}]
def representative (i : Fin {m}) : B := representativeData.getD i.val 0
def transportData : Array (Fin {m} × Fin {len(units)}) := #[{', '.join(f'({i}, {j})' for i,j in chart['transport'])}]
def transport (b : B) := transportData.getD b.val (0, 0)
def choiceData : Array (Array B) := {matrix(chart['choices'])}
def sizes (i : Fin {m}) : ℕ := (choiceData.getD i.val #[]).size
def choices (i : Fin {m}) (q : Fin (sizes i)) : B := (choiceData.getD i.val #[]).getD q.val 0
def stabilizerData : Array (Array (Fin {len(units)})) := {matrix(chart['stabilizers'])}
def stabilizers (i : Fin {m}) (j : Fin {width}) := (stabilizerData.getD i.val #[]).getD j.val 0
theorem chart_transport : ∀ b, maps (transport b).2 (representative (transport b).1) = b := by native_decide
theorem chart_fixed : ∀ i j, maps (stabilizers i j) (representative i) = representative i := by native_decide
theorem chart_choices : ∀ i b, (representative i = 0 → b = 0) →
    (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b := by native_decide
theorem chart_covered : ∀ p : (i : Fin {m}) → Fin (sizes i), ∃ k, ∀ b,
    values k b = maps (transport b).2 (choices (transport b).1 (p (transport b).1)) := by native_decide
theorem value_coverage : ∀ f : B → B, f 0 = 0 →
    (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f :=
  Magma.ProjectionKernelFamily.kernel_coverage_of_chart maps values representative transport
    sizes choices stabilizers chart_transport chart_fixed chart_choices chart_covered
'''
        start=core.index('theorem value_coverage :')
        end=core.index('\nabbrev Params :=',start)
        core=core[:start]+data+core[end:]
    stub=dict(d,base_moduli=[a],kernel_moduli=[b]);old=group_render(stub)
    tail=old[old.index('private def law'):]
    tail=tail.replace('Magma.ProjectionFamily.gen (A := A) (B := B)','Magma.ProjectionKernelFamily.gen (A := A) maps')
    tail=tail.replace('model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage\n    Magma.ProjectionFamily.family_generators','model (Magma.ProjectionKernelFamily.family_injective values value_injective)\n    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)\n    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)')
    result = core + tail
    if d.get('compiled_counts'):
        from definability_projection_kernel_native import integrate

        result = integrate(d, result)
    return result

def check(d):
    a=d['base_modulus'];b=d['kernel_modulus'];n=a*b;units=d['kernel_scalars'];assert n==d['order'] and all(math.gcd(h,b)==1 for h in units)
    chart=kernel_chart(b,units);fs=chart['functions']
    if b<=5:
        brute=[list(f) for f in itertools.product(range(b),repeat=b) if f[0]==0 and all(f[h*x%b]==h*f[x]%b for h in units for x in range(b))]
        assert fs==brute
    if d.get('unary_chart'):assert d['unary_chart']=={k:v for k,v in chart.items() if k!='functions'}
    assert fs==d['kernel_functions'];size=(a*len(fs))**a;assert size==d['family_count']
    codes=np.arange(size);g=np.empty((size,a),dtype=np.uint16);h=np.empty((size,a),dtype=np.uint16);div=1
    for i in range(a):g[:,i]=codes//div%a;div*=a
    for i in range(a):h[:,i]=codes//div%len(fs);div*=len(fs)
    f=g[:,np.arange(n)%a]+a*np.array(fs)[h[:,np.arange(n)%a],np.arange(n)//a]
    G=np.array([[(x%a+y%a)%a+a*((x//a+y//a)%b) for y in range(n)] for x in range(n)]);inv=np.array([next(y for y in range(n) if G[x,y]==0) for x in range(n)]);diff=G[inv[:,None],np.arange(n)[None,:]]
    T=G[np.arange(n)[None,:,None],f[:,diff]].astype(np.uint16)
    assert len({tuple(row) for row in f})==size
    for gen in [np.arange(n)%a]+[np.arange(n)%a+a*(u*(np.arange(n)//a)%b) for u in units]:assert np.array_equal(gen[T],T[:,gen[:,None],gen[None,:]])
    counts={law:len(model_indices(E,T,law)) for law in sorted({e[key] for e in d['candidates'] for key in ['source','target']})}
    for e in d['candidates']:assert counts[e['source']]==e['source_count'] and counts[e['target']]==e['target_count']
    print(d['namespace'],'complete family',size,'full-assignment counts',counts,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--only');args=p.parse_args()
    for path in sorted((ROOT/'data').glob('definability_projection_kernel_count*.json')):
        d=json.loads(path.read_text())
        if args.only and args.only not in d['namespace']:continue
        check(d);s=render(d);target=ROOT/'equational_theories/Definability/Generated'/f'{d["namespace"]}.lean'
        if args.write:target.write_text(s)
        else:assert target.read_text()==s
        if d.get('compiled_counts'):
            from definability_projection_kernel_native import render_native

            native = ROOT / 'defsearch/DefOrbit/Generated' / f'Native{d["namespace"]}.lean'
            text = render_native(d)
            if args.write:
                native.parent.mkdir(parents=True, exist_ok=True)
                native.write_text(text)
            else:
                assert native.read_text() == text, f'Regenerate {native} with --write'

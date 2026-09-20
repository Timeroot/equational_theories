#!/usr/bin/env python3
"""Check complete projection families over a possibly noncommutative group."""
import argparse,json,itertools
from pathlib import Path
import numpy as np
from definability_orbit_certificates_check import matrix
from definability_ring_counts_check import term
from definability_counting_upgrades_check import model_indices
from spectrum_generate import load_equations,variables
ROOT=Path(__file__).resolve().parents[1];E=load_equations()

def render(d):
    ns=d['namespace'];a=len(d['base_table']);b=d['kernel_modulus']
    s=f'''import equational_theories.Definability.LeftProjectionCounting
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by left translations and a group projection. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}
def A := Fin {a}
instance : Fintype A := inferInstanceAs (Fintype (Fin {a}))
instance : DecidableEq A := inferInstanceAs (DecidableEq (Fin {a}))
instance (n : ℕ) : OfNat A n := inferInstanceAs (OfNat (Fin {a}) n)
instance : Inhabited A := ⟨0⟩
def baseData : Array (Array A) := {matrix(d['base_table'])}
def inverseData : Array A := #[{', '.join(map(str,d['base_inverse']))}]
instance : Add A := ⟨fun x y => (baseData.getD x.val #[]).getD y.val 0⟩
instance : Zero A := ⟨0⟩
instance : Neg A := ⟨fun x => inverseData.getD x.val 0⟩
instance : AddGroup A := AddGroup.ofLeftAxioms (by native_decide) (by native_decide) (by native_decide)
abbrev B := ZMod {b}
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.LeftProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (Equiv.addLeft a) :=
  Magma.LeftProjectionFamily.family_generators p (.inl a)
theorem move_zero : ∀ a : A × B, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

'''
    counts={e[key]:e[key+'_count'] for e in d['candidates'] for key in ['source','target']}
    for law,count in sorted(counts.items()):
        l,r=E[law-1];k=1+max('xyzuvw'.index(v) for v in variables(l)|variables(r))
        s+=f'''private def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r)}⟩
private theorem count{law} : Fintype.card {{p : Params // PointTest (0 : A × B) (model p) law{law}}} = {count} := by native_decide

'''
    s+=f'end Magma.{ns}\n\nopen Magma.{ns}\n\n'
    for e in d['candidates']:
        source,target=e['source'],e['target'];k=1+max('xyzuvw'.index(v) for t in E[target-1] for v in variables(t));name=f'Equation{target}_not_termStructuralFromFin_Equation{source}_{ns[0].lower()+ns[1:]}'
        s+=f'''theorem {name} : ¬ Law{target}.TermStructuralFromFin Law{source} := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.LeftProjectionFamily.gen (A := A) (B := B))
    model Magma.LeftProjectionFamily.family_injective Magma.LeftProjectionFamily.coverage
    Magma.LeftProjectionFamily.family_generators
    (fun p => PointTest (0 : A × B) (model p) law{source})
    (fun p => PointTest (0 : A × B) (model p) law{target})
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat {k} i))
  · rw [count{source}, count{target}]
    decide

#print axioms {name}

'''
    for name,axioms in d.get('axioms',{}).items():s=s.replace('#print axioms '+name+'\n','/-- info: '+axioms+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+name+'\n')
    return s

def check(d):
    GA=np.array(d['base_table']);a=len(GA);b=d['kernel_modulus'];n=a*b;assert n==d['order'];R=np.arange(a)
    assert np.array_equal(GA[0],R) and np.array_equal(GA[:,0],R)
    for x,y,z in itertools.product(R,repeat=3):assert GA[GA[x,y],z]==GA[x,GA[y,z]]
    inv=np.array(d['base_inverse']);assert np.all(GA[inv,R]==0) and np.all(GA[R,inv]==0)
    size=a**a*b**(n-a);assert size==d['family_count'];codes=np.arange(size);f=np.empty((size,n),dtype=np.uint16);div=1
    for x in range(a):f[:,x]=codes//div%a;div*=a
    for x in range(a,n):f[:,x]=f[:,x%a]+a*(codes//div%b);div*=b
    G=np.array([[GA[x%a,y%a]+a*((x//a+y//a)%b) for y in range(n)] for x in range(n)]);gi=np.array([next(y for y in range(n) if G[x,y]==0) for x in range(n)]);diff=G[gi[:,None],np.arange(n)[None,:]]
    class Tables:
        shape=(size,n,n)
        def __len__(self):
            return size
        def __getitem__(self,key):
            i,x,y=key
            return G[x,f[i,diff[x,y]]]
    T=Tables();counts={law:len(model_indices(E,T,law)) for law in sorted({e[key] for e in d['candidates'] for key in ['source','target']})}
    for e in d['candidates']:assert counts[e['source']]==e['source_count'] and counts[e['target']]==e['target_count']
    print(d['namespace'],'complete family',size,'full-assignment counts',counts,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');args=p.parse_args()
    for path in sorted((ROOT/'data').glob('definability_left_projection_count*.json')):
        d=json.loads(path.read_text());check(d);s=render(d);target=ROOT/'equational_theories/Definability/Generated'/f'{d["namespace"]}.lean'
        if args.write:target.write_text(s)
        else:assert target.read_text()==s

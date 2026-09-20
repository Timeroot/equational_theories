#!/usr/bin/env python3
"""Check complete families preserved by left translations and group endomorphisms."""
import json,sys,math
from pathlib import Path
from definability_orbit_certificates_check import arr,matrix
from definability_ring_counts_check import term
from spectrum_generate import load_equations,variables
E=load_equations()
def render(d):
 ns=d['namespace'];n=d['order'];m=len(d['maps']);r=len(d['coordinates']);size=d['family_count'];fuel=size.bit_length()+1
 s=f'''import equational_theories.Definability.EndomorphismFamilyCounting
import Mathlib.Algebra.Group.MinimalAxioms

/-! Complete left-translation families restricted by noninvertible endomorphisms. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.{ns}
def A := Fin {n}
instance : Fintype A := inferInstanceAs (Fintype (Fin {n}))
instance : DecidableEq A := inferInstanceAs (DecidableEq (Fin {n}))
instance (n : ℕ) : OfNat A n := inferInstanceAs (OfNat (Fin {n}) n)
instance : Inhabited A := ⟨0⟩
def groupData : Array (Array A) := {matrix(d['group_table'])}
def inverseData : Array A := {arr(d['inverse'])}
instance : Add A := ⟨fun x y => (groupData.getD x.val #[]).getD y.val 0⟩
instance : Zero A := ⟨0⟩
instance : Neg A := ⟨fun x => inverseData.getD x.val 0⟩
instance : AddGroup A := AddGroup.ofLeftAxioms (by native_decide) (by native_decide) (by native_decide)
def mapData : Array (Array A) := {matrix(d['maps'])}
def mapFunction (i : Fin {m}) (x : A) : A := (mapData.getD i.val #[]).getD x.val 0
theorem map_zero : ∀ i, mapFunction i 0 = 0 := by native_decide
theorem map_add : ∀ i x y, mapFunction i (x + y) = mapFunction i x + mapFunction i y := by native_decide
def maps (i : Fin {m}) : A →+ A where
  toFun := mapFunction i
  map_zero' := map_zero i
  map_add' := map_add i

def valueData : Array (Array A) := {matrix(d['functions'])}
def values (i : Fin {size}) (x : A) : A := (valueData.getD i.val #[]).getD x.val 0
def coordinateData : Array A := {arr(d['coordinates'])}
def coordinate (i : Fin {r}) : A := coordinateData.getD i.val 0
def transportData : Array (Fin {r} × Fin {m}) := #[{', '.join(f'({i}, {j})' for i,j in d['transport'])}]
def transport (x : A) := transportData.getD x.val (0, 0)
def row (p : Fin {r} → A) (x : A) : A := maps (transport x).2 (p (transport x).1)
def key (f : A → A) : ℕ := (Finset.univ : Finset (Fin {n})).sum (fun x => (f x).val * {n} ^ x.val)
def keyData : Array ℕ := {arr(d['function_keys'])}
def findKey (key lo hi : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := keyData.getD mid 0
      if key = v then mid
      else if key < v then findKey key lo mid fuel
      else findKey key (mid + 1) hi fuel
    else 0
def recover (f : A → A) : Fin {size} := ⟨findKey (key f) 0 {size} {fuel} % {size}, Nat.mod_lt _ (by decide)⟩
def cover (p : Fin {r} → A) : Fin {size} := recover (row p)
theorem transport_correct : ∀ x, maps (transport x).2 (coordinate (transport x).1) = x := by native_decide
theorem cover_correct : ∀ p : Fin {r} → A,
    (∀ i x, maps i (row p x) = row p (maps i x)) → ∀ x, values (cover p) x = row p x := by native_decide
theorem recovery_correct : ∀ k, recover (values k) = k := by native_decide
theorem values_injective : Function.Injective values := by
  intro p q h
  have h := congrArg recover h
  simpa only [recovery_correct] using h
theorem values_commute : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
theorem values_coverage : ∀ f : A → A, (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f :=
  Magma.EndomorphismFamily.function_coverage_of_coordinates maps values coordinate transport
    transport_correct cover cover_correct
@[implicit_reducible] def model (p : Fin {size}) : Magma A := Magma.EndomorphismFamily.fam values p
theorem translations (p : Fin {size}) (a : A) : (model p).IsEndo (Equiv.addLeft a) :=
  Magma.EndomorphismFamily.family_generators maps values values_commute p (.inl a)
theorem move_zero : ∀ a : A, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

'''
 counts={e[k]:e[k+'_count'] for e in d['candidates'] for k in ['source','target']}
 for law,count in sorted(counts.items()):
  l,r0=E[law-1];k=1+max('xyzuvw'.index(v) for v in variables(l)|variables(r0))
  s+=f'''private def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r0)}⟩
private theorem count{law} : Fintype.card {{p : Fin {size} // PointTest (0 : A) (model p) law{law}}} = {count} := by native_decide

'''
 s+=f'end Magma.{ns}\n\nopen Magma.{ns}\n\n'
 for e in d['candidates']:
  a,b=e['source'],e['target'];k=1+max('xyzuvw'.index(v) for t in E[b-1] for v in variables(t));name=f'Equation{b}_not_termStructuralFromFin_Equation{a}_{ns[0].lower()+ns[1:]}'
  s+=f'''theorem {name} : ¬ Law{b}.TermStructuralFromFin Law{a} := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law{a})
    (fun p => PointTest (0 : A) (model p) law{b})
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat {k} i))
  · rw [count{a}, count{b}]
    decide

#print axioms {name}

'''
 for name,axioms in d.get('axioms',{}).items():s=s.replace('#print axioms '+name+'\n','/-- info: '+axioms+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+name+'\n')
 return s

def check(d):
    import itertools
    import numpy as np
    from definability_counting_upgrades_check import model_indices
    n=d['order'];G=np.array(d['group_table']);maps=np.array(d['maps']);ids=np.arange(n)
    assert G.shape==(n,n) and maps.shape[1]==n
    assert np.array_equal(G[0],ids) and np.array_equal(G[:,0],ids)
    assert np.all((G>=0)&(G<n)) and np.all((maps>=0)&(maps<n))
    for x,y,z in itertools.product(ids,repeat=3):assert G[G[x,y],z]==G[x,G[y,z]]
    inverse=np.array(d['inverse']);assert np.all(G[ids,inverse]==0) and np.all(G[inverse,ids]==0)
    for h in maps:assert h[0]==0 and np.array_equal(h[G],G[h[:,None],h[None,:]])
    rep=np.array(d['coordinates']);tr=np.array(d['transport']);r=len(rep)
    assert len(set(rep))==r and tr.shape==(n,2)
    assert np.array_equal(maps[tr[:,1],rep[tr[:,0]]],ids)
    size=n**r;assert d['coordinate_count']==size
    functions=[]
    for lo in range(0,size,50000):
        codes=np.arange(lo,min(lo+50000,size));p=(codes[:,None]//(n**np.arange(r)))%n
        f=maps[tr[:,1],p[:,tr[:,0]]];good=np.ones(len(codes),dtype=bool)
        for h in maps:
            active=np.flatnonzero(good);good[active]&=(h[f[active]]==f[active][:,h]).all(axis=1)
        functions.extend(f[good].tolist())
    code=lambda row:sum(int(v)*n**i for i,v in enumerate(row))
    functions.sort(key=code)
    assert functions==d['functions'] and len({tuple(f) for f in functions})==len(functions)==d['family_count']
    assert [code(f) for f in functions]==d['function_keys']
    diff=G[inverse[:,None],ids[None,:]];T=G[ids[None,:,None],np.array(functions)[:,diff]].astype(np.uint16)
    for h in maps:assert np.array_equal(h[T],T[:,h[:,None],h[None,:]])
    counts={law:len(model_indices(E,T,law)) for law in sorted({e[k] for e in d['candidates'] for k in ['source','target']})}
    for e in d['candidates']:
        assert counts[e['source']]==e['source_count']>e['target_count']==counts[e['target']]
    print(d['namespace'],'complete family',len(functions),'full-assignment counts',counts,flush=True)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('--only');args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    for p in sorted((root/'data').glob('definability_endomorphism_count_*.json')):
        d=json.loads(p.read_text())
        if args.only and args.only not in d['namespace']:continue
        check(d);target=root/'equational_theories/Definability/Generated'/(d['namespace']+'.lean');text=render(d)
        if args.write:target.write_text(text)
        else:assert target.read_text()==text,target

#!/usr/bin/env python3
"""Check translation families also preserved by a noninvertible endomorphism."""
import itertools
import json
from pathlib import Path
import numpy as np
from definability_orbit_certificates_check import arr, matrix
from definability_counting_upgrades_check import model_indices
from spectrum_generate import load_equations, variables
ROOT = Path(__file__).resolve().parents[1]
E = load_equations()

def render(d):
    n=d['order'];size=len(d['functions']);ns=d['namespace'];assert n==4
    s=f'''import equational_theories.Definability.InvariantFamilyCounting

/-! A complete family preserved by translations and a noninvertible projection. -/
open Law Law.MagmaLaw
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}
def addData : Array (Array (Fin {n})) := {matrix(d['group_table'])}
def add (x y : Fin {n}) : Fin {n} := (addData.getD x.val #[]).getD y.val 0
def projectionData : Array (Fin {n}) := {arr(d['projection'])}
def projection (x : Fin {n}) : Fin {n} := projectionData.getD x.val 0
def functionData : Array (Array (Fin {n})) := {matrix(d['functions'])}
def function (i : Fin {size}) (x : Fin {n}) : Fin {n} :=
  (functionData.getD i.val #[]).getD x.val 0
def gen (i : Fin {n+1}) (x : Fin {n}) : Fin {n} :=
  if h : i.val < {n} then add ⟨i.val, h⟩ x else projection x
@[implicit_reducible] def fam (i : Fin {size}) : Magma (Fin {n}) :=
  ⟨fun x y => add x (function i (add x y))⟩

theorem add_zero : ∀ x, add x 0 = x := by decide
theorem add_cancel : ∀ x y, add x (add x y) = y := by decide
theorem projection_zero : projection 0 = 0 := by decide
theorem gen_translation (x : Fin {n}) : gen x.castSucc = add x := by
  funext y
  simp [gen, x.isLt]

theorem function_coverage : ∀ f : Fin {n} → Fin {n},
    (∀ x, projection (f x) = f (projection x)) → ∃ i, function i = f := by native_decide

theorem coverage (N : Magma (Fin {n})) (hg : ∀ i, N.IsEndo (gen i)) :
    ∃ i, fam i = N := by
  let f : Fin {n} → Fin {n} := fun x => N.op 0 x
  have hp : ∀ x, projection (f x) = f (projection x) := by
    intro x
    have ht := hg {n} 0 x
    change projection (N.op 0 x) = N.op (projection 0) (projection x) at ht
    simpa only [projection_zero] using ht
  obtain ⟨i, hi⟩ := function_coverage f hp
  refine ⟨i, ?_⟩
  apply congrArg Magma.mk
  funext x y
  change add x (function i (add x y)) = N.op x y
  rw [hi]
  have ht := hg x.castSucc 0 (add x y)
  rw [gen_translation] at ht
  simpa only [add_zero, add_cancel] using ht

theorem family_injective : Function.Injective (fun i : Fin {size} => (fam i).op) := by native_decide
theorem family_generators : ∀ i j, (fam i).IsEndo (gen j) := by native_decide

'''
    counts={e[key]:e[key+'_count'] for e in d['candidates'] for key in ['source','target']}
    for law,count in sorted(counts.items()):
        l,r=E[law-1];names=sorted(variables(l)|variables(r))
        def term(t):
            return t if isinstance(t,str) else f'((fam p).op {term(t[0])} {term(t[1])})'
        s+=f'''private def test{law} (p : Fin {size}) : Prop := ∀ {' '.join(names)} : Fin {n}, {term(l)} = {term(r)}
private instance (p : Fin {size}) : Decidable (test{law} p) := by unfold test{law}; infer_instance
private theorem count{law} : Fintype.card {{p : Fin {size} // test{law} p}} = {count} := by native_decide

'''
    s+=f'end Magma.{ns}\n\nopen Magma.{ns}\n\n'
    for e in d['candidates']:
        a,b=e['source'],e['target'];name=f'Equation{b}_not_termStructuralFromFin_Equation{a}_projectionEndomorphism4'
        s+=f'''theorem {name} : ¬ Law{b}.TermStructuralFromFin Law{a} := by
  apply Magma.InvariantFamily.not_termStructuralFromFin gen fam family_injective
    coverage family_generators (test{a}) (test{b})
  · intro p hp
    exact (@Law{a}.models_iff (Fin {n}) (fam p)).mpr hp
  · intro p hp
    exact (@Law{b}.models_iff (Fin {n}) (fam p)).mp hp
  · rw [count{a}, count{b}]
    decide

#print axioms {name}

'''
    for name,axioms in d.get('axioms',{}).items():
        s=s.replace('#print axioms '+name+'\n','/-- info: '+axioms+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+name+'\n')
    return s

def check(d):
    n=d['order'];G=np.array(d['group_table']);P=np.array(d['projection']);assert n==4
    assert np.array_equal(G,np.bitwise_xor(np.arange(n)[:,None],np.arange(n)[None,:]))
    assert np.array_equal(P[G],G[P[:,None],P[None,:]])
    fs=[list(f) for f in itertools.product(range(n),repeat=n) if all(P[f[x]]==f[P[x]] for x in range(n))]
    assert fs==d['functions']
    tables=np.array([G[np.arange(n)[:,None],np.array(f)[G]] for f in fs],dtype=np.uint16)
    assert len({tuple(t.flat) for t in tables})==len(tables)
    for g in [*G,P]:assert np.array_equal(g[tables],tables[:,g[:,None],g[None,:]])
    for e in d['candidates']:
        for key in ['source','target']:assert len(model_indices(E,tables,e[key]))==e[key+'_count']
    print('Checked all 256 row functions, the complete 16-operation family, and both obstructions.',flush=True)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    d=json.loads((ROOT/'data/definability_projection_endomorphism4.json').read_text());check(d)
    p=ROOT/'equational_theories/Definability/Generated'/f'{d["namespace"]}.lean';s=render(d)
    if args.write:p.write_text(s)
    else:assert p.read_text()==s

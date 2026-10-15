#!/usr/bin/env python3
"""Generate compact recovery obstructions from saved six-element binary clones."""
from pathlib import Path
import json,sys
from itertools import product
sys.path.insert(0,'scripts')
from spectrum_generate import load_equations,variables,evaluate
ROOT=Path(__file__).resolve().parent.parent
R=json.loads((ROOT/'data/definability_six_element_clones.json').read_text())['models'];E=load_equations()
S='''import equational_theories.Definability.Clone
import equational_theories.Definability.Invariant
import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import Mathlib.Tactic.FinCases

/-! Recovery obstructions from three six-element magmas with small binary clones.
Every target companion is a projection or has its image in a fixed small set.
Term composition preserves that alternative, whereas the source fails it. -/
open Law Law.MagmaLaw
namespace SmallCloneRanges

def ProjectionOrRange {G : Type} (S : Set G) (f : G → G → G) : Prop :=
  (∀ x y, f x y = x) ∨ (∀ x y, f x y = y) ∨ ∀ x y, f x y ∈ S
instance {G : Type} [Fintype G] [DecidableEq G] (S : Set G) [DecidablePred (· ∈ S)]
    (f : G → G → G) : Decidable (ProjectionOrRange S f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem invariant {G : Type} (S : Set G) (N : Magma G)
    (h : ProjectionOrRange S N.op) : N.IsCloneInvariant (ProjectionOrRange S) where
  fst := Or.inl (fun _ _ => rfl)
  snd := Or.inr (Or.inl (fun _ _ => rfl))
  comp := by
    intro f g hf hg
    rcases h with hl | hr | hs
    · simpa only [hl] using hf
    · simpa only [hr] using hg
    · exact Or.inr (Or.inr (fun x y => hs (f x y) (g x y)))

theorem obstruct {G : Type} [Finite G] {L A : NatMagmaLaw} (M : Magma G)
    (hM : @satisfies _ G M A) {I : Type} (C : I → Magma G) {i₁ i₂ comp}
    (hc : M.IsCloneFamily C i₁ i₂ comp) (S : Set G)
    (hm : ¬ ProjectionOrRange S M.op)
    (ht : ∀ i, @satisfies _ G (C i) L → ProjectionOrRange S (C i).op) :
    ¬ L.TermStructuralFromFin A := by
  intro h
  obtain ⟨N,hn,hf,hr⟩ := h M hM
  obtain ⟨i,rfl⟩ := hc.exists_eq hf
  exact hm ((invariant S (C i) (ht i hn)).of_termDefinable hr)

abbrev Point := Fin 6
'''
checks=[]
for model,source,support in [(27,1037,[]),(6,4541,[3,5]),(74,4541,[3,4,5])]:
 r=next(r for r in R if r['model']==model);T=r['tables'];nt=len(T);bad=r['recover'];lookup={tuple(t):i for i,t in enumerate(T)};M=T[r['source_index']]
 C=[[lookup[tuple(M[6*x+y] for x,y in zip(a,b))] for b in T] for a in T]
 def vec(v):return '!['+', '.join(map(str,v))+']'
 S+=f'\nnamespace Model{model}\n'
 S+=f'def table : Fin {nt} → Point → Point → Point :=\n  !['+',\n    '.join(vec([vec(t[k:k+6]) for k in range(0,36,6)]) for t in T)+']\n'
 S+=f'''@[implicit_reducible] def family (i : Fin {nt}) : Magma Point := ⟨table i⟩
@[implicit_reducible] def source : Magma Point := family {r['source_index']}
def compose : Fin {nt} → Fin {nt} → Fin {nt} :=
  !['''+',\n    '.join(vec(c) for c in C)+''']
theorem closed : source.IsCloneFamily family 0 1 compose where
  fst := by decide
  snd := by decide
  comp := by decide +kernel
'''
 S+=f'theorem source_law : @Equation{source} Point source := by decide\n'
 S+='def support : Set Point := {'+', '.join(map(str,support))+'}\n'
 S+='instance : DecidablePred (· ∈ support) := by unfold support; infer_instance\n'
 S+=f'''theorem source_outside : ¬ ProjectionOrRange support source.op := by decide
def bad : Fin 2 → Fin {nt} := {vec(bad)}
theorem coverage : ∀ i, ProjectionOrRange support (family i).op ∨ ∃ j, i = bad j := by decide
'''
 for _,b in r['negative_pairs']:
  if model==74 and b in [4364,4512,4531]:continue
  lhs,rhs=E[b-1];vs=sorted(variables(lhs)|variables(rhs),key='xyzw'.index)
  S+=f'\nprivate theorem exclude{b} : ∀ j, ¬ @Equation{b} Point (family (bad j)) := by\n  intro j h\n  fin_cases j\n'
  for k in bad:
   vals=next(v for v in product(range(6),repeat=len(vs)) if evaluate(lhs,dict(zip(vs,v)),T[k],6)!=evaluate(rhs,dict(zip(vs,v)),T[k],6))
   a,z=[evaluate(t,dict(zip(vs,vals)),T[k],6) for t in [lhs,rhs]]
   S+=f'  · exact (by decide : ({a} : Point) ≠ {z}) (h '+ ' '.join(map(str,vals))+')\n'
  name=f'Equation{b}_not_termStructuralFromFin_Equation{source}'
  S+=f'''\ntheorem {name} : ¬ Law{b}.TermStructuralFromFin Law{source} := by
  apply obstruct source ((@Law{source}.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude{b} j ((@Law{b}.models_iff Point (family (bad j))).mp hi))
'''
  checks.append(f'SmallCloneRanges.Model{model}.{name}')
 S+=f'\nend Model{model}\n'
S+='\nend SmallCloneRanges\n'
for name in checks:S+=f"\n/-- info: '{name}' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs (whitespace := lax) in\n#print axioms {name}\n"
import argparse
parser=argparse.ArgumentParser(description='Reproduce the small-clone range certificates; Lean checks every assertion.')
mode=parser.add_mutually_exclusive_group(required=True)
mode.add_argument('--check',action='store_true');mode.add_argument('--write',action='store_true')
args=parser.parse_args();out=ROOT/'equational_theories/Definability/SmallCloneRanges.lean'
if args.write:out.write_text(S)
elif out.read_text()!=S:raise SystemExit('Generated file differs; run --write.')
print('Checked three clone families and sixteen refutation generators.')

#!/usr/bin/env python3
"""Reproduce the two finite restriction families and their guarded Lean proofs."""
import json,sys,importlib
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from definability_weak_central_check import binary_clone,holds_1483
T=np.array(importlib.import_module('1485_structure_check').twisted32());entries=json.load(open('data/definability_weak_central_recovery_search.json'))['subclone_targets']
vec=lambda a:'!['+', '.join(vec(x) if isinstance(x,list) else str(x) for x in a)+']'
s='''import equational_theories.Definability.WeakCentralSource

/-! The two closed subsets in the recovery search admit exactly two E1483
restrictions apiece among the source term operations, giving four cases. -/
namespace Magma.WeakCentralRestrictions
open Magma.WeakCentralSource
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
for name,e in zip(['Two','Four'],entries[:2]):
 sub=e['sub'];k=len(sub);lookup={v:i for i,v in enumerate(sub)};M=np.array([[lookup[int(T[x,y])] for y in sub] for x in sub],dtype=np.uint8);C=binary_clone(M);ix={c.tobytes():i for i,c in enumerate(C)};comp=[[ix[M[a,b].tobytes()] for b in C] for a in C];targets=[i for i,c in enumerate(C) if holds_1483(c)];assert len(C)==16 and len(targets)==2
 s+=f'''
namespace {name}
def embed : Fin {k} → Fin 32 := {vec(sub)}
def table : Fin 16 → Fin {k} → Fin {k} → Fin {k} := {vec([c.tolist() for c in C])}
@[implicit_reducible] def fam (i : Fin 16) : Magma (Fin {k}) := ⟨table i⟩
def comp : Fin 16 → Fin 16 → Fin 16 := {vec(comp)}
def choices : Fin 2 → Fin 16 := {vec(targets)}
theorem embed_injective : Function.Injective embed := by decide
theorem projections : ∀ a b, (fam 0).op a b = a ∧ (fam 1).op a b = b := by decide
theorem composition : ∀ i j a b,
    source.op (embed ((fam i).op a b)) (embed ((fam j).op a b)) =
      embed ((fam (comp i j)).op a b) := by decide

theorem source_invariant : source.IsCloneInvariant (fun f =>
    ∃ i : Fin 16, ∀ a b, f (embed a) (embed b) = embed ((fam i).op a b)) where
  fst := ⟨0, fun a b => congrArg embed (projections a b).1.symm⟩
  snd := ⟨1, fun a b => congrArg embed (projections a b).2.symm⟩
  comp f g hf hg := by
    obtain ⟨i, hi⟩ := hf
    obtain ⟨j, hj⟩ := hg
    refine ⟨comp i j, ?_⟩
    intro a b
    dsimp only
    rw [hi, hj]
    exact composition i j a b

theorem restricted_law {{N : Magma (Fin 32)}} (i : Fin 16)
    (hr : ∀ a b, N.op (embed a) (embed b) = embed ((fam i).op a b))
    (h : @Equation1483 (Fin 32) N) : @Equation1483 (Fin {k}) (fam i) := by
  intro x y z
  apply embed_injective
  simpa only [hr] using h (embed x) (embed y) (embed z)

theorem target_indices : ∀ i : Fin 16,
    @Equation1483 (Fin {k}) (fam i) → ∃ j : Fin 2, i = choices j := by decide

theorem restriction_cases {{N : Magma (Fin 32)}}
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (h : @Equation1483 (Fin 32) N) :
    ∃ j : Fin 2, ∀ a b, N.op (embed a) (embed b) = embed ((fam (choices j)).op a b) := by
  obtain ⟨i, hi⟩ := source_invariant.of_termDefinable ht
  obtain ⟨j, rfl⟩ := target_indices i (restricted_law i hi h)
  exact ⟨j, hi⟩
#print axioms Magma.WeakCentralRestrictions.{name}.composition
#print axioms Magma.WeakCentralRestrictions.{name}.target_indices
#print axioms Magma.WeakCentralRestrictions.{name}.restriction_cases
end {name}
'''
s+='''
theorem four_cases {N : Magma (Fin 32)}
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (h : @Equation1483 (Fin 32) N) :
    ∃ i j : Fin 2,
      (∀ a b, N.op (Two.embed a) (Two.embed b) = Two.embed ((Two.fam (Two.choices i)).op a b)) ∧
      (∀ a b, N.op (Four.embed a) (Four.embed b) = Four.embed ((Four.fam (Four.choices j)).op a b)) := by
  obtain ⟨i, hi⟩ := Two.restriction_cases ht h
  obtain ⟨j, hj⟩ := Four.restriction_cases ht h
  exact ⟨i, j, hi, hj⟩
#print axioms Magma.WeakCentralRestrictions.four_cases
end Magma.WeakCentralRestrictions
'''
config=json.load(open(ROOT/'data/definability_weak_central_foundations.json'))['restrictions']
for name,axiom in config['axioms'].items():
    old='#print axioms '+name+'\n'
    assert s.count(old)==1,name
    s=s.replace(old,'/-- info: '+axiom+' -/\n#guard_msgs (whitespace := lax) in\n'+old)
output=ROOT/'equational_theories/Definability/WeakCentralRestrictions.lean'
if '--write' in sys.argv:output.write_text(s)
else:assert output.read_text()==s,'Regenerate with --write'
print('WeakCentralRestrictions: exact generated source checked')

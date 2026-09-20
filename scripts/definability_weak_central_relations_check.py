#!/usr/bin/env python3
"""Reproduce the source-compatible binary relations and guarded Lean proofs."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1]
D=json.load(open('data/definability_weak_central_recovery_search.json'))['relations'];D=[r for r in D if len(r)<1024];n=len(D);rows=',\n  '.join('['+', '.join(map(str,r))+']' for r in D)
s=f'''import equational_theories.Definability.WeakCentralSource

/-! Every term operation preserves each listed compatible binary relation.
The universal relation is omitted, since it imposes no constraint. -/

namespace Magma.WeakCentralRelations
open Magma.WeakCentralSource
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def relationCodes : Array (List Nat) := #[
  {rows}]

def decode (v : Nat) : Fin 32 × Fin 32 :=
  (⟨v/32%32, Nat.mod_lt _ (by decide)⟩, ⟨v%32, Nat.mod_lt _ (by decide)⟩)

def pairs (i : Fin {n}) : List (Fin 32 × Fin 32) :=
  (relationCodes.getD i.val []).map decode

def Preserves {{G : Type}} (f : G → G → G) (r : List (G × G)) : Prop :=
  ∀ a ∈ r, ∀ b ∈ r, (f a.1 b.1, f a.2 b.2) ∈ r

instance {{G : Type}} [DecidableEq G] (f : G → G → G) (r : List (G × G)) :
    Decidable (Preserves f r) := inferInstanceAs (Decidable (∀ a ∈ r, ∀ b ∈ r, _))

theorem source_relations : ∀ i : Fin {n}, Preserves source.op (pairs i) := by native_decide

theorem preserves_of_termDefinable {{G : Type}} {{M N : Magma G}} (r : List (G × G))
    (hc : Preserves M.op r)
    (h : @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ N.FinArityOp) :
    Preserves N.op r := by
  have hP : M.IsCloneInvariant (fun f => Preserves f r) :=
    {{ fst := fun a ha b hb => ha
      snd := fun a ha b hb => hb
      comp := by
        intro f g hf hg a ha b hb
        exact hc (f a.1 b.1, f a.2 b.2) (hf a ha b hb)
          (g a.1 b.1, g a.2 b.2) (hg a ha b hb) }}
  exact hP.of_termDefinable h

theorem target_relations {{N : Magma (Fin 32)}}
    (h : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp) :
    ∀ i : Fin {n}, Preserves N.op (pairs i) :=
  fun i => preserves_of_termDefinable (pairs i) (source_relations i) h

#print axioms Magma.WeakCentralRelations.source_relations
#print axioms Magma.WeakCentralRelations.preserves_of_termDefinable
#print axioms Magma.WeakCentralRelations.target_relations
end Magma.WeakCentralRelations
'''
config=json.load(open(ROOT/'data/definability_weak_central_foundations.json'))['relations']
assert n==config['relation_count'] and sum(map(len,D))==config['pair_count']
assert all(0<=x<1024 for row in D for x in row)
if config['ordinary']:s=s.replace('by native_decide','by decide')
for name,axiom in config['axioms'].items():
    old='#print axioms '+name+'\n'
    assert s.count(old)==1,name
    s=s.replace(old,'/-- info: '+axiom+' -/\n#guard_msgs (whitespace := lax) in\n'+old)
output=ROOT/'equational_theories/Definability/WeakCentralRelations.lean'
if '--write' in sys.argv:output.write_text(s)
else:assert output.read_text()==s,'Regenerate with --write'
print('WeakCentralRelations: exact generated source checked')

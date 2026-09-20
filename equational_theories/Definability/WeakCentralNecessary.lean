import equational_theories.Definability.WeakCentralRestrictions
import equational_theories.Definability.WeakCentralRelations
import equational_theories.Definability.FiniteFlavour

/-! Necessary conditions for recovering the 32-point E1485 source from an
E1483 term operation. These conditions have not been proved inconsistent.
The SAT encoding and its symmetry normalization require separate proofs. -/

namespace Magma.WeakCentralNecessary
open Magma.WeakCentralSource Magma.GenerationOrder
open Magma.WeakCentralRestrictions Magma.WeakCentralRelations
open Law Law.MagmaLaw

structure Conditions (N : Magma (Fin 32)) : Prop where
  law : @Equation1483 (Fin 32) N
  rotation : ∀ x y, N.op (WeakCentralSource.rotation x) (WeakCentralSource.rotation y) =
    WeakCentralSource.rotation (N.op x y)
  idempotents : ∀ x : Fin 32,
    N.op x x = x ↔ x = 11 ∨ x = 13 ∨ x = 21 ∨ x = 22 ∨ x = 26
  relations : ∀ i : Fin 174, Preserves N.op (pairs i)
  restrictions : ∃ i j : Fin 2,
    (∀ a b, N.op (Two.embed a) (Two.embed b) = Two.embed ((Two.fam (Two.choices i)).op a b)) ∧
    (∀ a b, N.op (Four.embed a) (Four.embed b) = Four.embed ((Four.fam (Four.choices j)).op a b))
  pair_order : Nonempty (Witness N.op pairSeeds)
  one_order : Nonempty (Witness N.op oneSeeds)
  three_order : Nonempty (Witness N.op threeSeeds)
  seven_order : Nonempty (Witness N.op sevenSeeds)

theorem conditions_of_mutual {N : Magma (Fin 32)}
    (h : @Equation1483 (Fin 32) N)
    (hf : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ source.FinArityOp) :
    Conditions N where
  law := h
  rotation := rotation_of_termDefinable hf
  idempotents := recovered_idempotents hf hr
  relations := target_relations hf
  restrictions := four_cases hf h
  pair_order := ⟨recovered_pair_order hr⟩
  one_order := ⟨finiteWitness_of_recovery oneSeeds hr one_generates⟩
  three_order := ⟨finiteWitness_of_recovery threeSeeds hr three_generates⟩
  seven_order := ⟨finiteWitness_of_recovery sevenSeeds hr seven_generates⟩

/-- Any positive answer to the finite term-structural question supplies a
model of all the conditions above. No inconsistency claim is made here. -/
theorem exists_conditions
    (h : TermStructuralFromFin Law1483 Law1485) :
    ∃ N : Magma (Fin 32), Conditions N := by
  obtain ⟨N, hN, hf, hr⟩ := h source ((@Law1485.models_iff (Fin 32) source).mpr source_law)
  exact ⟨N, conditions_of_mutual ((@Law1483.models_iff (Fin 32) N).mp hN) hf hr⟩

/-- info: 'Magma.WeakCentralNecessary.conditions_of_mutual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 source_relations._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms conditions_of_mutual
/-- info: 'Magma.WeakCentralNecessary.exists_conditions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 source_relations._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_conditions

end Magma.WeakCentralNecessary

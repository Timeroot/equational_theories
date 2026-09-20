import equational_theories.Definability.WeakCentralSource

/-! The two closed subsets in the recovery search admit exactly two E1483
restrictions apiece among the source term operations, giving four cases. -/
namespace Magma.WeakCentralRestrictions
open Magma.WeakCentralSource
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Two
def embed : Fin 2 → Fin 32 := ![0, 31]
def table : Fin 16 → Fin 2 → Fin 2 → Fin 2 := ![![![0, 0], ![1, 1]], ![![0, 1], ![0, 1]], ![![1, 1], ![0, 0]], ![![1, 1], ![1, 0]], ![![1, 0], ![1, 0]], ![![1, 1], ![1, 1]], ![![1, 0], ![1, 1]], ![![1, 1], ![0, 1]], ![![0, 0], ![0, 1]], ![![0, 1], ![1, 1]], ![![0, 0], ![0, 0]], ![![0, 1], ![0, 0]], ![![0, 0], ![1, 0]], ![![0, 1], ![1, 0]], ![![1, 0], ![0, 1]], ![![1, 0], ![0, 0]]]
@[implicit_reducible] def fam (i : Fin 16) : Magma (Fin 2) := ⟨table i⟩
def comp : Fin 16 → Fin 16 → Fin 16 := ![![2, 3, 5, 7, 7, 2, 2, 3, 3, 2, 5, 5, 7, 7, 3, 5], ![3, 4, 6, 6, 5, 4, 3, 4, 3, 4, 5, 6, 5, 6, 3, 5], ![5, 6, 0, 0, 9, 0, 9, 0, 5, 6, 5, 6, 5, 6, 9, 9], ![7, 6, 0, 8, 1, 8, 1, 0, 5, 14, 5, 6, 7, 14, 9, 9], ![7, 5, 9, 1, 1, 1, 1, 9, 5, 7, 5, 5, 7, 7, 9, 9], ![2, 4, 0, 8, 1, 10, 11, 12, 3, 15, 5, 6, 7, 14, 13, 9], ![2, 3, 9, 1, 1, 11, 11, 13, 3, 2, 5, 5, 7, 7, 13, 9], ![3, 4, 0, 0, 9, 12, 13, 12, 3, 4, 5, 6, 5, 6, 13, 9], ![3, 3, 5, 5, 5, 3, 3, 3, 3, 3, 5, 5, 5, 5, 3, 5], ![2, 4, 6, 14, 7, 15, 2, 4, 3, 15, 5, 6, 7, 14, 3, 5], ![5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], ![5, 6, 6, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 5], ![7, 5, 5, 7, 7, 7, 7, 5, 5, 7, 5, 5, 7, 7, 5, 5], ![7, 6, 6, 14, 7, 14, 7, 6, 5, 14, 5, 6, 7, 14, 5, 5], ![3, 3, 9, 9, 9, 13, 13, 13, 3, 3, 5, 5, 5, 5, 13, 9], ![5, 5, 9, 9, 9, 9, 9, 9, 5, 5, 5, 5, 5, 5, 9, 9]]
def choices : Fin 2 → Fin 16 := ![3, 15]
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

theorem restricted_law {N : Magma (Fin 32)} (i : Fin 16)
    (hr : ∀ a b, N.op (embed a) (embed b) = embed ((fam i).op a b))
    (h : @Equation1483 (Fin 32) N) : @Equation1483 (Fin 2) (fam i) := by
  intro x y z
  apply embed_injective
  simpa only [hr] using h (embed x) (embed y) (embed z)

theorem target_indices : ∀ i : Fin 16,
    @Equation1483 (Fin 2) (fam i) → ∃ j : Fin 2, i = choices j := by decide

theorem restriction_cases {N : Magma (Fin 32)}
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (h : @Equation1483 (Fin 32) N) :
    ∃ j : Fin 2, ∀ a b, N.op (embed a) (embed b) = embed ((fam (choices j)).op a b) := by
  obtain ⟨i, hi⟩ := source_invariant.of_termDefinable ht
  obtain ⟨j, rfl⟩ := target_indices i (restricted_law i hi h)
  exact ⟨j, hi⟩
/-- info: 'Magma.WeakCentralRestrictions.Two.composition' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Two.composition
/-- info: 'Magma.WeakCentralRestrictions.Two.target_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Two.target_indices
/-- info: 'Magma.WeakCentralRestrictions.Two.restriction_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Two.restriction_cases
end Two

namespace Four
def embed : Fin 4 → Fin 32 := ![5, 13, 21, 29]
def table : Fin 16 → Fin 4 → Fin 4 → Fin 4 := ![![![0, 0, 0, 0], ![1, 1, 1, 1], ![2, 2, 2, 2], ![3, 3, 3, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![3, 3, 3, 3], ![1, 1, 1, 1], ![2, 2, 2, 2], ![0, 0, 0, 0]], ![![3, 1, 3, 1], ![3, 1, 3, 1], ![2, 0, 2, 0], ![2, 0, 2, 0]], ![![3, 3, 2, 2], ![1, 1, 0, 0], ![3, 3, 2, 2], ![1, 1, 0, 0]], ![![3, 1, 2, 0], ![3, 1, 2, 0], ![3, 1, 2, 0], ![3, 1, 2, 0]], ![![1, 1, 1, 1], ![1, 1, 1, 1], ![2, 2, 2, 2], ![2, 2, 2, 2]], ![![2, 2, 2, 2], ![1, 1, 1, 1], ![2, 2, 2, 2], ![1, 1, 1, 1]], ![![1, 1, 0, 0], ![1, 1, 0, 0], ![3, 3, 2, 2], ![3, 3, 2, 2]], ![![2, 0, 2, 0], ![3, 1, 3, 1], ![2, 0, 2, 0], ![3, 1, 3, 1]], ![![2, 3, 2, 3], ![0, 1, 0, 1], ![2, 3, 2, 3], ![0, 1, 0, 1]], ![![2, 1, 2, 1], ![2, 1, 2, 1], ![2, 1, 2, 1], ![2, 1, 2, 1]], ![![0, 1, 0, 1], ![0, 1, 0, 1], ![2, 3, 2, 3], ![2, 3, 2, 3]], ![![1, 1, 3, 3], ![1, 1, 3, 3], ![0, 0, 2, 2], ![0, 0, 2, 2]], ![![1, 1, 2, 2], ![1, 1, 2, 2], ![1, 1, 2, 2], ![1, 1, 2, 2]], ![![0, 0, 2, 2], ![1, 1, 3, 3], ![0, 0, 2, 2], ![1, 1, 3, 3]]]
@[implicit_reducible] def fam (i : Fin 16) : Magma (Fin 4) := ⟨table i⟩
def comp : Fin 16 → Fin 16 → Fin 16 := ![![2, 4, 7, 10, 7, 10, 2, 7, 2, 10, 7, 10, 2, 4, 4, 4], ![3, 5, 9, 11, 9, 11, 3, 9, 3, 11, 9, 11, 3, 5, 5, 5], ![6, 8, 0, 12, 0, 12, 6, 0, 6, 12, 0, 12, 6, 8, 8, 8], ![6, 8, 0, 12, 0, 12, 6, 0, 6, 12, 0, 12, 6, 8, 8, 8], ![13, 14, 15, 1, 15, 1, 13, 15, 13, 1, 15, 1, 13, 14, 14, 14], ![13, 14, 15, 1, 15, 1, 13, 15, 13, 1, 15, 1, 13, 14, 14, 14], ![6, 8, 0, 12, 0, 12, 6, 0, 6, 12, 0, 12, 6, 8, 8, 8], ![2, 4, 7, 10, 7, 10, 2, 7, 2, 10, 7, 10, 2, 4, 4, 4], ![13, 14, 15, 1, 15, 1, 13, 15, 13, 1, 15, 1, 13, 14, 14, 14], ![2, 4, 7, 10, 7, 10, 2, 7, 2, 10, 7, 10, 2, 4, 4, 4], ![3, 5, 9, 11, 9, 11, 3, 9, 3, 11, 9, 11, 3, 5, 5, 5], ![3, 5, 9, 11, 9, 11, 3, 9, 3, 11, 9, 11, 3, 5, 5, 5], ![3, 5, 9, 11, 9, 11, 3, 9, 3, 11, 9, 11, 3, 5, 5, 5], ![6, 8, 0, 12, 0, 12, 6, 0, 6, 12, 0, 12, 6, 8, 8, 8], ![13, 14, 15, 1, 15, 1, 13, 15, 13, 1, 15, 1, 13, 14, 14, 14], ![2, 4, 7, 10, 7, 10, 2, 7, 2, 10, 7, 10, 2, 4, 4, 4]]
def choices : Fin 2 → Fin 16 := ![3, 4]
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

theorem restricted_law {N : Magma (Fin 32)} (i : Fin 16)
    (hr : ∀ a b, N.op (embed a) (embed b) = embed ((fam i).op a b))
    (h : @Equation1483 (Fin 32) N) : @Equation1483 (Fin 4) (fam i) := by
  intro x y z
  apply embed_injective
  simpa only [hr] using h (embed x) (embed y) (embed z)

theorem target_indices : ∀ i : Fin 16,
    @Equation1483 (Fin 4) (fam i) → ∃ j : Fin 2, i = choices j := by decide

theorem restriction_cases {N : Magma (Fin 32)}
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (h : @Equation1483 (Fin 32) N) :
    ∃ j : Fin 2, ∀ a b, N.op (embed a) (embed b) = embed ((fam (choices j)).op a b) := by
  obtain ⟨i, hi⟩ := source_invariant.of_termDefinable ht
  obtain ⟨j, rfl⟩ := target_indices i (restricted_law i hi h)
  exact ⟨j, hi⟩
/-- info: 'Magma.WeakCentralRestrictions.Four.composition' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Four.composition
/-- info: 'Magma.WeakCentralRestrictions.Four.target_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Four.target_indices
/-- info: 'Magma.WeakCentralRestrictions.Four.restriction_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.Four.restriction_cases
end Four

theorem four_cases {N : Magma (Fin 32)}
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (h : @Equation1483 (Fin 32) N) :
    ∃ i j : Fin 2,
      (∀ a b, N.op (Two.embed a) (Two.embed b) = Two.embed ((Two.fam (Two.choices i)).op a b)) ∧
      (∀ a b, N.op (Four.embed a) (Four.embed b) = Four.embed ((Four.fam (Four.choices j)).op a b)) := by
  obtain ⟨i, hi⟩ := Two.restriction_cases ht h
  obtain ⟨j, hj⟩ := Four.restriction_cases ht h
  exact ⟨i, j, hi, hj⟩
/-- info: 'Magma.WeakCentralRestrictions.four_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralRestrictions.four_cases
end Magma.WeakCentralRestrictions

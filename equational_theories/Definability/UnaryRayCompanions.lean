import equational_theories.Definability.Invariant
import equational_theories.Definability.DiagRow

/-! Square-row recovery for E1133, and first-order companions of the two unary rays.

The general E1133 → E1167 term-structural question remains open. The recovery
identity below proves only the recovery half of that proposed construction;
`ThreeRowTree.lean` refutes its target-law half on an infinite model.
The concrete E1167 ray does have an E1133 companion with first-order recovery.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

namespace SquareRowRecovery

variable {G : Type} (M : Magma G) (h : @Equation1133 G M)
local infixl:70 " * " => M.op

@[implicit_reducible] def transform : Magma G := ⟨fun x y => (x * x) * y⟩

include h in
theorem invol (x y : G) : x * (x * y) = y := by
  have h₁ := h y x (x * (x * x))
  have h₂ := h x x x
  grind

include h in
theorem row_law (x y z : G) : (y * (z * y)) * x = y * x := by
  have e := congrArg (M.op y) (h x y z)
  simpa only [invol M h] using e.symm

include h in
theorem row_after (x y z : G) : ((z * y) * y) * x = (z * y) * x := by
  simpa only [invol M h] using row_law M h x (z * y) z

include h in
theorem square_unsquare (x : G) :
    ((x * x) * x) * ((x * x) * x) = x := by
  rw [row_after M h _ x x, invol M h]

include h in
theorem recover (x y : G) :
    (transform (transform M)).op x y = M.op x y := by
  change (((x * x) * x) * ((x * x) * x)) * y = x * y
  rw [square_unsquare M h]

include h in
theorem transformed_square_injective :
    Function.Injective (fun x => (transform M).op x x) := by
  apply Function.LeftInverse.injective (g := fun x => M.op x x)
  exact square_unsquare M h

end SquareRowRecovery

namespace UnaryPermutationRecovery

@[implicit_reducible] def ray : Magma ℕ where
  op x y := if y % 2 = x % 2 then y + 1 else y - 1

theorem ray_law : @Equation1167 ℕ ray := by
  intro x y z
  dsimp [ray, Magma.op]
  split_ifs <;> omega

theorem ray_not_surjective_square : ¬ Function.Surjective (fun x => ray.op x x) := by
  intro h
  obtain ⟨x, hx⟩ := h 0
  simp [Magma.op] at hx

@[implicit_reducible] def predecessorRay : Magma ℕ where
  op x y := if y % 2 = x % 2 then y - 1 else y + 1

theorem predecessorRay_law : @Equation1133 ℕ predecessorRay := by
  intro x y z
  dsimp [predecessorRay, Magma.op]
  split_ifs <;> omega

theorem predecessorRay_not_injective_square :
    ¬ Function.Injective (fun x => predecessorRay.op x x) := by
  intro h
  have := h (a₁ := 0) (a₂ := 1) (by decide)
  omega

theorem predecessorRay_is_transform (x y : ℕ) :
    predecessorRay.op x y = (SquareRowRecovery.transform ray).op x y := by
  simp only [Magma.op]
  split_ifs <;> omega

/-- The nontrivial predecessor preimage recovers the missing successor row. -/
theorem ray_recovery (x y z : ℕ) :
    z = ray.op x y ↔ ∃ u, predecessorRay.op u u = x ∧ u ≠ x ∧
      z = predecessorRay.op u y := by
  constructor
  · intro hz
    refine ⟨x + 1, ?_, by omega, ?_⟩
    · simp [Magma.op]
    · rw [hz]
      dsimp [ray, predecessorRay, Magma.op]
      split_ifs <;> omega
  · rintro ⟨u, hu, hne, hz⟩
    have hux : u = x + 1 := by
      change (if u % 2 = u % 2 then u - 1 else u + 1) = x at hu
      rw [if_pos rfl] at hu
      omega
    subst u
    rw [hz]
    dsimp [ray, predecessorRay, Magma.op]
    split_ifs <;> omega

private abbrev tm {G : Type} {α : Type}
    (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term α) :=
  Functions.apply₂ (Sum.inl ()) a b

attribute [local instance] instFOStructure

/-- `∃ u, u*u = x ∧ u ≠ x ∧ z = u*y`, in the predecessor-ray language. -/
private def recoveryFormula :
    (MagmaLanguage.withConstants (∅ : Set ℕ)).Formula (Option (Fin 2)) :=
  let x : (MagmaLanguage.withConstants (∅ : Set ℕ)).Term (Option (Fin 2) ⊕ Fin 1) :=
    .var (.inl (some 0))
  let y : (MagmaLanguage.withConstants (∅ : Set ℕ)).Term (Option (Fin 2) ⊕ Fin 1) :=
    .var (.inl (some 1))
  let z : (MagmaLanguage.withConstants (∅ : Set ℕ)).Term (Option (Fin 2) ⊕ Fin 1) :=
    .var (.inl none)
  let u : (MagmaLanguage.withConstants (∅ : Set ℕ)).Term (Option (Fin 2) ⊕ Fin 1) :=
    .var (.inr 0)
  BoundedFormula.ex ((tm u u).bdEqual x ⊓ ∼(u.bdEqual x) ⊓ z.bdEqual (tm u y))

private theorem realize_recoveryFormula (v : Option (Fin 2) → ℕ) (xs : Fin 0 → ℕ) :
    letI := predecessorRay.FOStructure
    BoundedFormula.Realize recoveryFormula v xs ↔
      ∃ u, predecessorRay.op u u = v (some 0) ∧ u ≠ v (some 0) ∧
        v none = predecessorRay.op u (v (some 1)) := by
  letI := predecessorRay.FOStructure
  simp [recoveryFormula, tm, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Magma.FOStructure_funMap', Magma.FinArityOp, Fin.snoc,
    and_assoc]

theorem ray_has_1133_fo_companion : Law1133.StructuralOnMagma ray := by
  refine ⟨predecessorRay, (@Law1133.models_iff ℕ predecessorRay).mpr
    predecessorRay_law, ?_, ?_⟩
  · have ht : @Set.TermDefinable _ ∅ MagmaLanguage ray.FOStructure _
        predecessorRay.FinArityOp := by
      refine ⟨tm (tm (.var 0) (.var 0)) (.var 1), ?_⟩
      funext v
      exact predecessorRay_is_transform (v 0) (v 1)
    letI := ray.FOStructure
    exact ht.definable_tupleGraph
  · refine ⟨recoveryFormula, ?_⟩
    letI := predecessorRay.FOStructure
    ext v
    change (ray.op (v (some 0)) (v (some 1)) = v none) ↔
      Formula.Realize recoveryFormula v
    simp only [Formula.Realize, realize_recoveryFormula]
    rw [eq_comm]
    exact ray_recovery _ _ _

/-- This particular companion cannot recover the successor ray by a term:
all of its terms preserve the singleton `{0}`. This does not exclude other companions. -/
theorem predecessorRay_cannot_term_recover_ray :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage predecessorRay.FOStructure _ ray.FinArityOp := by
  intro h
  have hi : predecessorRay.IsCloneInvariant (fun f => f 0 0 = 0) := {
    fst := rfl
    snd := rfl
    comp := by
      intro f g hf hg
      change predecessorRay.op (f 0 0) (g 0 0) = 0
      rw [hf, hg]
      rfl }
  have hb := hi.of_termDefinable h
  change 1 = 0 at hb
  omega

end UnaryPermutationRecovery

/-- info: 'SquareRowRecovery.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SquareRowRecovery.recover
/-- info: 'UnaryPermutationRecovery.ray_has_1133_fo_companion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnaryPermutationRecovery.ray_has_1133_fo_companion
/-- info: 'UnaryPermutationRecovery.predecessorRay_cannot_term_recover_ray' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnaryPermutationRecovery.predecessorRay_cannot_term_recover_ray

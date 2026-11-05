import equational_theories.Parastrophes.Attributes
import equational_theories.Confluence
import equational_theories.Generated.Greedy.Eq124Idempotent
import equational_theories.Generated.Greedy.Eq670Idempotent
import equational_theories.Generated.Greedy.Eq1082Idempotent
import equational_theories.Generated.Greedy.Eq1288Idempotent
import equational_theories.Generated.Greedy.Eq1315Idempotent

/-! Countable countermodels for the remaining infinite bijectivity questions. -/
namespace Parastrophes
open Law FreeMagma Confluence

namespace Normal1085
variable {α : Type} [DecidableEq α]

/-- Delete the E1085 pattern, leaving all other trees unchanged. -/
def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ ((x₁ ⋆ (y₂ ⋆ y₃)) ⋆ x₂)) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ x₁ = x₂ then x₁ else m
  | m => m

instance : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    repeat' split
    any_goals subterm

local macro "unchanged" : tactic => `(tactic| (
  unfold rule
  split
  · injections
    subst_eqs
    split
    · exfalso
      casesm* _ ∧ _
      subst_eqs
    · rfl
  · rfl
))

@[simp] theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by unchanged
@[simp] theorem rule_xyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by unchanged
@[simp] theorem rule_xyyx (x y : FreeMagma α) :
    rule ((x ⋆ (y ⋆ y)) ⋆ x) = (x ⋆ (y ⋆ y)) ⋆ x := by unchanged
@[simp] theorem rule_law (x y : FreeMagma α) :
    rule (y ⋆ ((x ⋆ (y ⋆ y)) ⋆ x)) = x := by simp [rule]

theorem law : Equation1085 (ConfMagma (@rule Nat _)) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp [Magma.op, bu, hx, hy]

end Normal1085

/-- A free normal-form E1085 model has distinct inputs with the same value
in the row of a generator. Surjectivity is forced by E1085, but injectivity is not. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1085_all :
    ¬ SideQuasigroupLaw .all Law1085 .left := by
  intro h
  let G := ConfMagma (@Normal1085.rule Nat inferInstance)
  have hQ := h G inferInstance trivial ((@Law1085.models_iff G _).mpr Normal1085.law)
  let a : G := (0 : Nat)
  let b : G := (1 : Nat)
  have hc : a ◇ (((a ◇ b) ◇ (a ◇ a)) ◇ (a ◇ b)) = a ◇ b :=
    (Normal1085.law (a ◇ b) a).symm
  have hn : ((a ◇ b) ◇ (a ◇ a)) ◇ (a ◇ b) ≠ b := by decide
  exact hn ((hQ a).1 hc)

/-- An idempotent E124 countermodel also satisfies E1322 and retains its
row collision. Thus the finite left-bijectivity theorem does not extend. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1322_all :
    ¬ SideQuasigroupLaw .all Law1322 .left := by
  intro h
  let e := Eq124Idempotent.collisionSeed
  have hE : @Equation1322 Nat e.toMagma := by
    intro x y
    change x = e.complFun y (e.complFun (e.complFun (e.complFun y y) x) x)
    rw [e.toMagma_idempotent]
    exact e.toMagma_equation124 x y
  have hQ := h Nat e.toMagma trivial ((@Law1322.models_iff Nat e.toMagma).mpr hE)
  have h1 := e.of_R 0 1 3 (by unfold e Eq124Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq124Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- A countable idempotent E670 model retains two equal entries in its zero row. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup670_all :
    ¬ SideQuasigroupLaw .all Law670 .left := by
  intro h
  let e := Eq670Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law670.models_iff Nat e.toMagma).mpr e.toMagma_equation670)
  have h1 := e.of_R 0 1 3 (by unfold e Eq670Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq670Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- A countable idempotent E1082 model retains two equal entries in its zero row. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1082_all :
    ¬ SideQuasigroupLaw .all Law1082 .left := by
  intro h
  let e := Eq1082Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1082.models_iff Nat e.toMagma).mpr e.toMagma_equation1082)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1082Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1082Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- A countable idempotent E1288 model retains two equal entries in its zero row. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1288_all :
    ¬ SideQuasigroupLaw .all Law1288 .left := by
  intro h
  let e := Eq1288Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1288.models_iff Nat e.toMagma).mpr e.toMagma_equation1288)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1288Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1288Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- An idempotent countable E1315 model can have distinct entries in the same row. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1315_all :
    ¬ SideQuasigroupLaw .all Law1315 .left := by
  intro h
  let e := Eq1315Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1315.models_iff Nat e.toMagma).mpr e.toMagma_equation1315)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1315Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1315Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

end Parastrophes

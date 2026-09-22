import equational_theories.Spectrum.MendelsohnSix
import equational_theories.Spectrum.Generated.Modular
import equational_theories.Spectrum.Shapes
import equational_theories.Superposition
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The exact spectrum of E66

Squaring twists every E66 magma into an idempotent semisymmetric quasigroup.
-/

namespace Spectrum
namespace Mendelsohn

variable {Q : Type*}

/-- The squaring twist of E66. No finiteness assumption is needed. -/
def ofEquation66 [Magma Q] (h : Equation66 Q) : Mendelsohn Q := by
  have e9 (x y : Q) : y ◇ (x ◇ (y ◇ y)) = x := (h x y).symm
  have e11 (x : Q) : (x ◇ x) ◇ (x ◇ x) = x := superpose e9 e9
  have e12 (x y : Q) : (x ◇ x) ◇ (y ◇ x) = y := superpose e11 e9
  have e16 (x y : Q) : x ◇ x = ((y ◇ x) ◇ (y ◇ x)) ◇ y := superpose e12 e12
  have e18 (x y : Q) : (y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x)) = (y ◇ y) ◇ x :=
    superpose e9 e16
  refine ⟨fun x y => (x ◇ y) ◇ (x ◇ y), e11, ?_⟩
  intro x y
  change (y ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y))) = x
  rw [e18, e12]

theorem semi' (M : Mendelsohn Q) (x y : Q) : M.op (M.op x y) x = y := by
  simpa only [M.semi] using M.semi y (M.op x y)

/-- Directed pairs rotate in triples; the fixed pairs are exactly the diagonal. -/
theorem card_mod_three [Fintype Q] (M : Mendelsohn Q) :
    Fintype.card Q % 3 = 0 ∨ Fintype.card Q % 3 = 1 := by
  classical
  let f : Function.End (Q × Q) := fun p => (p.2, M.op p.1 p.2)
  have hf : f ^ 3 ^ 1 = 1 := by
    funext ⟨x,y⟩
    change (M.op y (M.op x y), M.op (M.op x y) (M.op y (M.op x y))) = (x,y)
    rw [M.semi, M.semi']
  let e : f.fixedPoints ≃ Q := {
    toFun := fun p => p.val.1
    invFun := fun x => ⟨(x,x), by simp [Function.IsFixedPt, f, M.idem]⟩
    left_inv := by
      intro p
      apply Subtype.ext
      have hp : f p.val = p.val := p.property
      have := congrArg Prod.fst hp
      exact Prod.ext rfl this.symm
    right_inv := fun _ => rfl }
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_congr e, Fintype.card_prod] at h
  have hh : (Fintype.card Q % 3) * (Fintype.card Q % 3) % 3 = Fintype.card Q % 3 := by
    simpa only [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using h
  have hb := Nat.mod_lt (Fintype.card Q) (by omega : 0 < 3)
  rcases (show Fintype.card Q % 3 = 0 ∨ Fintype.card Q % 3 = 1 ∨ Fintype.card Q % 3 = 2 by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · norm_num [h] at hh

end Mendelsohn

open Law Law.MagmaLaw

/-- Explicit models at every positive order congruent to zero or one modulo
three, except six. -/
theorem models_66 {n : ℕ} (h : n ∈ residues 3 {0,1} {6}) : Law66.HasModel n := by
  simp only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton] at h
  by_cases h1 : n = 1
  · subst n; exact hasModel_one Law66
  by_cases h7 : n = 7
  · subst n; exact model_66_7
  have hk : 0 < n / 3 ∧ n / 3 ≠ 2 := by omega
  obtain ⟨Q, f, ⟨L⟩, hc⟩ := IdempotentLatin.exists_card (n/3) hk.1 hk.2
  letI : Fintype Q := f
  rcases h.2.1 with h0 | h1
  · exact hasModel_of_card (Mendelsohn.bose L).magma
      ((@Law66.models_iff _ (Mendelsohn.bose L).magma).mpr (Mendelsohn.bose L).equation66)
      (by simp only [Fintype.card_prod, Fintype.card_fin, hc]; omega)
  · exact hasModel_of_card (Mendelsohn.bosePlus L).magma
      ((@Law66.models_iff _ (Mendelsohn.bosePlus L).magma).mpr (Mendelsohn.bosePlus L).equation66)
      (by simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, hc]; omega)

/-- The directed-pair count and the six-point obstruction give all restrictions. -/
theorem orders_66 {n : ℕ} (h : n ∈ Law66.spectrum) : n ∈ residues 3 {0,1} {6} := by
  obtain ⟨hn, M, hM⟩ := h
  letI := M
  have he : Equation66 (Fin n) := (@Law66.models_iff _ M).mp hM
  have hm := (Mendelsohn.ofEquation66 he).card_mod_three
  simp only [Fintype.card_fin] at hm
  have h6 : n ≠ 6 := by
    intro e
    subst n
    exact MendelsohnSix.impossible (Mendelsohn.ofEquation66 he)
  simpa only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton] using
    And.intro hn (And.intro hm h6)

/-- The complete positive finite spectrum of E66. -/
theorem exact_66 : Law66.spectrum = residues 3 {0,1} {6} := by
  ext n
  exact ⟨orders_66, fun h => ⟨h.1, models_66 h⟩⟩

spectrum_assert exact_66 complete

end Spectrum

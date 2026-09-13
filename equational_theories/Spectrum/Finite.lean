import equational_theories.Spectrum.Basic
import Mathlib.Tactic.FinCases

/-!
Exhaustive small-model certificates, using ordinary kernel reduction.
The four entries of a two-element multiplication table enumerate all 16 magmas.
-/

open Law

namespace Spectrum

@[implicit_reducible]
def table2 (a b c d : Fin 2) : Magma (Fin 2) :=
  ⟨fun x y => if x = 0 then (if y = 0 then a else b) else (if y = 0 then c else d)⟩

theorem eq_table2 (M : Magma (Fin 2)) :
    M = table2 (M.op 0 0) (M.op 0 1) (M.op 1 0) (M.op 1 1) := by
  cases M with
  | mk op =>
    congr 1
    funext x y
    fin_cases x <;> fin_cases y <;> rfl

/-- Use the equation's existing `models_iff` theorem to keep the finite test computable. -/
theorem not_two_of_equation (L : NatMagmaLaw) (P : Magma (Fin 2) → Prop)
    (hP : ∀ M, @satisfies _ (Fin 2) M L ↔ P M)
    (h : ∀ a b c d, ¬ P (table2 a b c d)) : ¬ L.HasModel 2 := by
  rintro ⟨M, hM⟩
  have hm := (hP M).mp hM
  rw [eq_table2 M] at hm
  exact h _ _ _ _ hm

end Spectrum

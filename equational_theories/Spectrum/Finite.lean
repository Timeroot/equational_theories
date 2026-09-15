import equational_theories.Spectrum.Basic
import Mathlib.Tactic.FinCases

/-!
Every operation on `Fin 2` or `Fin 3` is determined by its four or nine entries.
Completeness is proved once; exclusions use compact `native_decide` loops over
16 or 19683 tables, instead of generated case trees. Direct entry enumeration
avoids the repeated exponentiation/division overhead of base-n table codes.
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

@[implicit_reducible]
def table3 (a b c d e f g h i : Fin 3) : Magma (Fin 3) :=
  ⟨fun x y => if x = 0 then (if y = 0 then a else if y = 1 then b else c)
    else if x = 1 then (if y = 0 then d else if y = 1 then e else f)
    else (if y = 0 then g else if y = 1 then h else i)⟩

theorem eq_table3 (M : Magma (Fin 3)) :
    M = table3 (M.op 0 0) (M.op 0 1) (M.op 0 2)
      (M.op 1 0) (M.op 1 1) (M.op 1 2) (M.op 2 0) (M.op 2 1) (M.op 2 2) := by
  cases M with
  | mk op =>
    congr 1
    funext x y
    fin_cases x <;> fin_cases y <;> rfl

theorem not_three_of_equation (L : NatMagmaLaw) (P : Magma (Fin 3) → Prop)
    (hP : ∀ M, @satisfies _ (Fin 3) M L ↔ P M)
    (h : ∀ a b c d e f g h i, ¬ P (table3 a b c d e f g h i)) : ¬ L.HasModel 3 := by
  rintro ⟨M, hM⟩
  have hm := (hP M).mp hM
  rw [eq_table3 M] at hm
  exact h _ _ _ _ _ _ _ _ _ hm

/-- Use the equation's existing `models_iff` theorem to keep the finite test computable. -/
theorem not_two_of_equation (L : NatMagmaLaw) (P : Magma (Fin 2) → Prop)
    (hP : ∀ M, @satisfies _ (Fin 2) M L ↔ P M)
    (h : ∀ a b c d, ¬ P (table2 a b c d)) : ¬ L.HasModel 2 := by
  rintro ⟨M, hM⟩
  have hm := (hP M).mp hM
  rw [eq_table2 M] at hm
  exact h _ _ _ _ hm

end Spectrum

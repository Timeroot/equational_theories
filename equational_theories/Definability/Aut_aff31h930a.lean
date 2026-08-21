import equational_theories.Definability.Aut_aff31h930a_data

/-! # The data lemmas for the group of order 930 on Fin 31 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aff31h930a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aff31h930a

namespace aff31h930a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aff31h930a

theorem aff31h930aM677_models : @satisfies _ (Fin 31) aff31h930aM677 Law677 :=
  (@Law677.models_iff (Fin 31) aff31h930aM677).mpr (by native_decide)

theorem aff31h930aM677_endo : ∀ i, aff31h930aM677.IsEndo (aff31h930a.E i) := by native_decide

import equational_theories.Definability.Prn_prn7h6a_data

/-! # The data lemmas for the group of order 6 on Fin 7 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn7h6a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn7h6a

namespace prn7h6a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn7h6a

theorem prn7h6aM1313_models : @satisfies _ (Fin 7) prn7h6aM1313 Law1313 :=
  (@Law1313.models_iff (Fin 7) prn7h6aM1313).mpr (by native_decide)

theorem prn7h6aM1313_endo : ∀ i, prn7h6aM1313.IsEndo (prn7h6a.E i) := by decide

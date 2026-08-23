import equational_theories.Definability.Prn_prn9h6a_data

/-! # The data lemmas for the group of order 6 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h6a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h6a

namespace prn9h6a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h6a

theorem prn9h6aM667_models : @satisfies _ (Fin 9) prn9h6aM667 Law667 :=
  (@Law667.models_iff (Fin 9) prn9h6aM667).mpr (by native_decide)

theorem prn9h6aM667_endo : ∀ i, prn9h6aM667.IsEndo (prn9h6a.E i) := by decide

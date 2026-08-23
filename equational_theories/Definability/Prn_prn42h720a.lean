import equational_theories.Definability.Prn_prn42h720a_data

/-! # The data lemmas for the group of order 720 on Fin 42 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace prn42h720a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end prn42h720a

namespace prn42h720a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end prn42h720a

theorem prn42h720aM3279_models : @satisfies _ (Fin 42) prn42h720aM3279 Law3279 :=
  (@Law3279.models_iff (Fin 42) prn42h720aM3279).mpr (by native_decide)

theorem prn42h720aM3279_endo : ∀ i, prn42h720aM3279.IsEndo (prn42h720a.E i) := by native_decide

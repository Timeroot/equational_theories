import equational_theories.Definability.Prn_prn8h4a_data

/-! # The data lemmas for the group of order 4 on Fin 8 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h4a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h4a

namespace prn8h4a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h4a

theorem prn8h4aM1485_models : @satisfies _ (Fin 8) prn8h4aM1485 Law1485 :=
  (@Law1485.models_iff (Fin 8) prn8h4aM1485).mpr (by native_decide)

theorem prn8h4aM1485_endo : ∀ i, prn8h4aM1485.IsEndo (prn8h4a.E i) := by decide

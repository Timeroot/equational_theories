import equational_theories.Definability.Prn_prn8h7a_data

/-! # The data lemmas for the group of order 7 on Fin 8 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h7a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h7a

namespace prn8h7a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h7a

theorem prn8h7aM1083_models : @satisfies _ (Fin 8) prn8h7aM1083 Law1083 :=
  (@Law1083.models_iff (Fin 8) prn8h7aM1083).mpr (by native_decide)

theorem prn8h7aM1083_endo : ∀ i, prn8h7aM1083.IsEndo (prn8h7a.E i) := by decide

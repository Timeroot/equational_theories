import equational_theories.Definability.Prn_prn9h8b_data

/-! # The data lemmas for the group of order 8 on Fin 9 (#2) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h8b

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h8b

namespace prn9h8b

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h8b

theorem prn9h8bM1110_models : @satisfies _ (Fin 9) prn9h8bM1110 Law1110 :=
  (@Law1110.models_iff (Fin 9) prn9h8bM1110).mpr (by native_decide)

theorem prn9h8bM1110_endo : ∀ i, prn9h8bM1110.IsEndo (prn9h8b.E i) := by decide

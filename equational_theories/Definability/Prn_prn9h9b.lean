import equational_theories.Definability.Prn_prn9h9b_data

/-! # The data lemmas for the group of order 9 on Fin 9 (#2) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h9b

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h9b

namespace prn9h9b

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h9b

theorem prn9h9bM501_models : @satisfies _ (Fin 9) prn9h9bM501 Law501 :=
  (@Law501.models_iff (Fin 9) prn9h9bM501).mpr (by native_decide)

theorem prn9h9bM501_endo : ∀ i, prn9h9bM501.IsEndo (prn9h9b.E i) := by decide

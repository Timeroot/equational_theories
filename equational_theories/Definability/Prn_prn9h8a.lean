import equational_theories.Definability.Prn_prn9h8a_data

/-! # The data lemmas for the group of order 8 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h8a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h8a

namespace prn9h8a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h8a

theorem prn9h8aM467_models : @satisfies _ (Fin 9) prn9h8aM467 Law467 :=
  (@Law467.models_iff (Fin 9) prn9h8aM467).mpr (by native_decide)

theorem prn9h8aM467_endo : ∀ i, prn9h8aM467.IsEndo (prn9h8a.E i) := by decide

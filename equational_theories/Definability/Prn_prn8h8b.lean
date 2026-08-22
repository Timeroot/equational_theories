import equational_theories.Definability.Prn_prn8h8b_data

/-! # The data lemmas for the group of order 8 on Fin 8 (#2) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h8b

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h8b

namespace prn8h8b

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h8b

theorem prn8h8bM4415_models : @satisfies _ (Fin 8) prn8h8bM4415 Law4415 :=
  (@Law4415.models_iff (Fin 8) prn8h8bM4415).mpr (by native_decide)

theorem prn8h8bM4415_endo : ∀ i, prn8h8bM4415.IsEndo (prn8h8b.E i) := by decide

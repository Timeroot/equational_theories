import equational_theories.Definability.Prn_prn8h4b_data

/-! # The data lemmas for the group of order 4 on Fin 8 (#2) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h4b

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h4b

namespace prn8h4b

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h4b

theorem prn8h4bM873_models : @satisfies _ (Fin 8) prn8h4bM873 Law873 :=
  (@Law873.models_iff (Fin 8) prn8h4bM873).mpr (by native_decide)

theorem prn8h4bM873_endo : ∀ i, prn8h4bM873.IsEndo (prn8h4b.E i) := by decide

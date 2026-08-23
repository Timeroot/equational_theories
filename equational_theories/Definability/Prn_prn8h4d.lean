import equational_theories.Definability.Prn_prn8h4d_data

/-! # The data lemmas for the group of order 4 on Fin 8 (#4) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h4d

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h4d

namespace prn8h4d

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h4d

theorem prn8h4dM873_models : @satisfies _ (Fin 8) prn8h4dM873 Law873 :=
  (@Law873.models_iff (Fin 8) prn8h4dM873).mpr (by native_decide)

theorem prn8h4dM873_endo : ∀ i, prn8h4dM873.IsEndo (prn8h4d.E i) := by decide

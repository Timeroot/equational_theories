import equational_theories.Definability.Prn_prn8h2a_data

/-! # The data lemmas for the group of order 2 on Fin 8 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h2a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h2a

namespace prn8h2a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h2a

theorem prn8h2aM873_models : @satisfies _ (Fin 8) prn8h2aM873 Law873 :=
  (@Law873.models_iff (Fin 8) prn8h2aM873).mpr (by native_decide)

theorem prn8h2aM873_endo : ∀ i, prn8h2aM873.IsEndo (prn8h2a.E i) := by decide

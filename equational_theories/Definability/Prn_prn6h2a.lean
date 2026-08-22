import equational_theories.Definability.Prn_prn6h2a_data

/-! # The data lemmas for the group of order 2 on Fin 6 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn6h2a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn6h2a

namespace prn6h2a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn6h2a

theorem prn6h2aM1480_models : @satisfies _ (Fin 6) prn6h2aM1480 Law1480 :=
  (@Law1480.models_iff (Fin 6) prn6h2aM1480).mpr (by native_decide)

theorem prn6h2aM1480_endo : ∀ i, prn6h2aM1480.IsEndo (prn6h2a.E i) := by decide

theorem prn6h2aM3269_models : @satisfies _ (Fin 6) prn6h2aM3269 Law3269 :=
  (@Law3269.models_iff (Fin 6) prn6h2aM3269).mpr (by native_decide)

theorem prn6h2aM3269_endo : ∀ i, prn6h2aM3269.IsEndo (prn6h2a.E i) := by decide

theorem prn6h2aM3279_models : @satisfies _ (Fin 6) prn6h2aM3279 Law3279 :=
  (@Law3279.models_iff (Fin 6) prn6h2aM3279).mpr (by native_decide)

theorem prn6h2aM3279_endo : ∀ i, prn6h2aM3279.IsEndo (prn6h2a.E i) := by decide

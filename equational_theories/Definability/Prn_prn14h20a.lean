import equational_theories.Definability.Prn_prn14h20a_data

/-! # The data lemmas for the group of order 20 on Fin 14 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn14h20a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn14h20a

namespace prn14h20a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn14h20a

theorem prn14h20aM3558_models : @satisfies _ (Fin 14) prn14h20aM3558 Law3558 :=
  (@Law3558.models_iff (Fin 14) prn14h20aM3558).mpr (by native_decide)

theorem prn14h20aM3558_endo : ∀ i, prn14h20aM3558.IsEndo (prn14h20a.E i) := by decide

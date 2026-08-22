import equational_theories.Definability.Prn_prn6h3a_data

/-! # The data lemmas for the group of order 3 on Fin 6 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn6h3a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn6h3a

namespace prn6h3a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn6h3a

theorem prn6h3aM1480_models : @satisfies _ (Fin 6) prn6h3aM1480 Law1480 :=
  (@Law1480.models_iff (Fin 6) prn6h3aM1480).mpr (by native_decide)

theorem prn6h3aM1480_endo : ∀ i, prn6h3aM1480.IsEndo (prn6h3a.E i) := by decide

theorem prn6h3aM1682_models : @satisfies _ (Fin 6) prn6h3aM1682 Law1682 :=
  (@Law1682.models_iff (Fin 6) prn6h3aM1682).mpr (by native_decide)

theorem prn6h3aM1682_endo : ∀ i, prn6h3aM1682.IsEndo (prn6h3a.E i) := by decide

theorem prn6h3aM1719_models : @satisfies _ (Fin 6) prn6h3aM1719 Law1719 :=
  (@Law1719.models_iff (Fin 6) prn6h3aM1719).mpr (by native_decide)

theorem prn6h3aM1719_endo : ∀ i, prn6h3aM1719.IsEndo (prn6h3a.E i) := by decide

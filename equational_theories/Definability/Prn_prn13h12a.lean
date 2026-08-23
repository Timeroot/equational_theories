import equational_theories.Definability.Prn_prn13h12a_data

/-! # The data lemmas for the group of order 12 on Fin 13 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn13h12a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn13h12a

namespace prn13h12a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn13h12a

theorem prn13h12aM467_models : @satisfies _ (Fin 13) prn13h12aM467 Law467 :=
  (@Law467.models_iff (Fin 13) prn13h12aM467).mpr (by native_decide)

theorem prn13h12aM467_endo : ∀ i, prn13h12aM467.IsEndo (prn13h12a.E i) := by decide

theorem prn13h12aM704_models : @satisfies _ (Fin 13) prn13h12aM704 Law704 :=
  (@Law704.models_iff (Fin 13) prn13h12aM704).mpr (by native_decide)

theorem prn13h12aM704_endo : ∀ i, prn13h12aM704.IsEndo (prn13h12a.E i) := by decide

theorem prn13h12aM1516_models : @satisfies _ (Fin 13) prn13h12aM1516 Law1516 :=
  (@Law1516.models_iff (Fin 13) prn13h12aM1516).mpr (by native_decide)

theorem prn13h12aM1516_endo : ∀ i, prn13h12aM1516.IsEndo (prn13h12a.E i) := by decide

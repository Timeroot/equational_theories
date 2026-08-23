import equational_theories.Definability.Prn_prn8h4c_data

/-! # The data lemmas for the group of order 4 on Fin 8 (#3) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h4c

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h4c

namespace prn8h4c

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h4c

theorem prn8h4cM14_models : @satisfies _ (Fin 8) prn8h4cM14 Law14 :=
  (@Law14.models_iff (Fin 8) prn8h4cM14).mpr (by native_decide)

theorem prn8h4cM14_endo : ∀ i, prn8h4cM14.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM477_models : @satisfies _ (Fin 8) prn8h4cM477 Law477 :=
  (@Law477.models_iff (Fin 8) prn8h4cM477).mpr (by native_decide)

theorem prn8h4cM477_endo : ∀ i, prn8h4cM477.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM680_models : @satisfies _ (Fin 8) prn8h4cM680 Law680 :=
  (@Law680.models_iff (Fin 8) prn8h4cM680).mpr (by native_decide)

theorem prn8h4cM680_endo : ∀ i, prn8h4cM680.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM692_models : @satisfies _ (Fin 8) prn8h4cM692 Law692 :=
  (@Law692.models_iff (Fin 8) prn8h4cM692).mpr (by native_decide)

theorem prn8h4cM692_endo : ∀ i, prn8h4cM692.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM1276_models : @satisfies _ (Fin 8) prn8h4cM1276 Law1276 :=
  (@Law1276.models_iff (Fin 8) prn8h4cM1276).mpr (by native_decide)

theorem prn8h4cM1276_endo : ∀ i, prn8h4cM1276.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM1519_models : @satisfies _ (Fin 8) prn8h4cM1519 Law1519 :=
  (@Law1519.models_iff (Fin 8) prn8h4cM1519).mpr (by native_decide)

theorem prn8h4cM1519_endo : ∀ i, prn8h4cM1519.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM3472_models : @satisfies _ (Fin 8) prn8h4cM3472 Law3472 :=
  (@Law3472.models_iff (Fin 8) prn8h4cM3472).mpr (by native_decide)

theorem prn8h4cM3472_endo : ∀ i, prn8h4cM3472.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM3588_models : @satisfies _ (Fin 8) prn8h4cM3588 Law3588 :=
  (@Law3588.models_iff (Fin 8) prn8h4cM3588).mpr (by native_decide)

theorem prn8h4cM3588_endo : ∀ i, prn8h4cM3588.IsEndo (prn8h4c.E i) := by decide

theorem prn8h4cM4273_models : @satisfies _ (Fin 8) prn8h4cM4273 Law4273 :=
  (@Law4273.models_iff (Fin 8) prn8h4cM4273).mpr (by native_decide)

theorem prn8h4cM4273_endo : ∀ i, prn8h4cM4273.IsEndo (prn8h4c.E i) := by decide

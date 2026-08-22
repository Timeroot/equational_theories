import equational_theories.Definability.Prn_prn8h4a_data

/-! # The data lemmas for the group of order 4 on Fin 8 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h4a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h4a

namespace prn8h4a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h4a

theorem prn8h4aM14_models : @satisfies _ (Fin 8) prn8h4aM14 Law14 :=
  (@Law14.models_iff (Fin 8) prn8h4aM14).mpr (by native_decide)

theorem prn8h4aM14_endo : ∀ i, prn8h4aM14.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM477_models : @satisfies _ (Fin 8) prn8h4aM477 Law477 :=
  (@Law477.models_iff (Fin 8) prn8h4aM477).mpr (by native_decide)

theorem prn8h4aM477_endo : ∀ i, prn8h4aM477.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM680_models : @satisfies _ (Fin 8) prn8h4aM680 Law680 :=
  (@Law680.models_iff (Fin 8) prn8h4aM680).mpr (by native_decide)

theorem prn8h4aM680_endo : ∀ i, prn8h4aM680.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM692_models : @satisfies _ (Fin 8) prn8h4aM692 Law692 :=
  (@Law692.models_iff (Fin 8) prn8h4aM692).mpr (by native_decide)

theorem prn8h4aM692_endo : ∀ i, prn8h4aM692.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM1276_models : @satisfies _ (Fin 8) prn8h4aM1276 Law1276 :=
  (@Law1276.models_iff (Fin 8) prn8h4aM1276).mpr (by native_decide)

theorem prn8h4aM1276_endo : ∀ i, prn8h4aM1276.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM1519_models : @satisfies _ (Fin 8) prn8h4aM1519 Law1519 :=
  (@Law1519.models_iff (Fin 8) prn8h4aM1519).mpr (by native_decide)

theorem prn8h4aM1519_endo : ∀ i, prn8h4aM1519.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM3472_models : @satisfies _ (Fin 8) prn8h4aM3472 Law3472 :=
  (@Law3472.models_iff (Fin 8) prn8h4aM3472).mpr (by native_decide)

theorem prn8h4aM3472_endo : ∀ i, prn8h4aM3472.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM3588_models : @satisfies _ (Fin 8) prn8h4aM3588 Law3588 :=
  (@Law3588.models_iff (Fin 8) prn8h4aM3588).mpr (by native_decide)

theorem prn8h4aM3588_endo : ∀ i, prn8h4aM3588.IsEndo (prn8h4a.E i) := by decide

theorem prn8h4aM4273_models : @satisfies _ (Fin 8) prn8h4aM4273 Law4273 :=
  (@Law4273.models_iff (Fin 8) prn8h4aM4273).mpr (by native_decide)

theorem prn8h4aM4273_endo : ∀ i, prn8h4aM4273.IsEndo (prn8h4a.E i) := by decide

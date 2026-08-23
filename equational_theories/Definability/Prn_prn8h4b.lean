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

theorem prn8h4bM14_models : @satisfies _ (Fin 8) prn8h4bM14 Law14 :=
  (@Law14.models_iff (Fin 8) prn8h4bM14).mpr (by native_decide)

theorem prn8h4bM14_endo : ∀ i, prn8h4bM14.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM477_models : @satisfies _ (Fin 8) prn8h4bM477 Law477 :=
  (@Law477.models_iff (Fin 8) prn8h4bM477).mpr (by native_decide)

theorem prn8h4bM477_endo : ∀ i, prn8h4bM477.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM680_models : @satisfies _ (Fin 8) prn8h4bM680 Law680 :=
  (@Law680.models_iff (Fin 8) prn8h4bM680).mpr (by native_decide)

theorem prn8h4bM680_endo : ∀ i, prn8h4bM680.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM692_models : @satisfies _ (Fin 8) prn8h4bM692 Law692 :=
  (@Law692.models_iff (Fin 8) prn8h4bM692).mpr (by native_decide)

theorem prn8h4bM692_endo : ∀ i, prn8h4bM692.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM1276_models : @satisfies _ (Fin 8) prn8h4bM1276 Law1276 :=
  (@Law1276.models_iff (Fin 8) prn8h4bM1276).mpr (by native_decide)

theorem prn8h4bM1276_endo : ∀ i, prn8h4bM1276.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM1519_models : @satisfies _ (Fin 8) prn8h4bM1519 Law1519 :=
  (@Law1519.models_iff (Fin 8) prn8h4bM1519).mpr (by native_decide)

theorem prn8h4bM1519_endo : ∀ i, prn8h4bM1519.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM3472_models : @satisfies _ (Fin 8) prn8h4bM3472 Law3472 :=
  (@Law3472.models_iff (Fin 8) prn8h4bM3472).mpr (by native_decide)

theorem prn8h4bM3472_endo : ∀ i, prn8h4bM3472.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM3588_models : @satisfies _ (Fin 8) prn8h4bM3588 Law3588 :=
  (@Law3588.models_iff (Fin 8) prn8h4bM3588).mpr (by native_decide)

theorem prn8h4bM3588_endo : ∀ i, prn8h4bM3588.IsEndo (prn8h4b.E i) := by decide

theorem prn8h4bM4273_models : @satisfies _ (Fin 8) prn8h4bM4273 Law4273 :=
  (@Law4273.models_iff (Fin 8) prn8h4bM4273).mpr (by native_decide)

theorem prn8h4bM4273_endo : ∀ i, prn8h4bM4273.IsEndo (prn8h4b.E i) := by decide

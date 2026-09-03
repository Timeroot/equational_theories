import equational_theories.Definability.Shp_shp9h6s2k3_data

/-! # The data lemmas for the shape 2 shuffle on Fin 9 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace shp9h6s2k3

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end shp9h6s2k3

namespace shp9h6s2k3

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end shp9h6s2k3

theorem shp9h6s2k3M667_models : @satisfies _ (Fin 9) shp9h6s2k3M667 Law667 :=
  (@Law667.models_iff (Fin 9) shp9h6s2k3M667).mpr (by native_decide)

theorem shp9h6s2k3M667_endo : ∀ i, shp9h6s2k3M667.IsEndo (shp9h6s2k3.E i) := by native_decide

theorem shp9h6s2k3M3279_models : @satisfies _ (Fin 9) shp9h6s2k3M3279 Law3279 :=
  (@Law3279.models_iff (Fin 9) shp9h6s2k3M3279).mpr (by native_decide)

theorem shp9h6s2k3M3279_endo : ∀ i, shp9h6s2k3M3279.IsEndo (shp9h6s2k3.E i) := by native_decide

import equational_theories.Definability.Aut_mau9h72a_data

/-! # The data lemmas for the group of order 72 on Fin 9 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace mau9h72a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end mau9h72a

namespace mau9h72a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end mau9h72a

theorem mau9h72aM167_models : @satisfies _ (Fin 9) mau9h72aM167 Law167 :=
  (@Law167.models_iff (Fin 9) mau9h72aM167).mpr (by native_decide)

theorem mau9h72aM167_endo : ∀ i, mau9h72aM167.IsEndo (mau9h72a.E i) := by native_decide

theorem mau9h72aM501_models : @satisfies _ (Fin 9) mau9h72aM501 Law501 :=
  (@Law501.models_iff (Fin 9) mau9h72aM501).mpr (by native_decide)

theorem mau9h72aM501_endo : ∀ i, mau9h72aM501.IsEndo (mau9h72a.E i) := by native_decide

theorem mau9h72aM1682_models : @satisfies _ (Fin 9) mau9h72aM1682 Law1682 :=
  (@Law1682.models_iff (Fin 9) mau9h72aM1682).mpr (by native_decide)

theorem mau9h72aM1682_endo : ∀ i, mau9h72aM1682.IsEndo (mau9h72a.E i) := by native_decide

theorem mau9h72aM3675_models : @satisfies _ (Fin 9) mau9h72aM3675 Law3675 :=
  (@Law3675.models_iff (Fin 9) mau9h72aM3675).mpr (by native_decide)

theorem mau9h72aM3675_endo : ∀ i, mau9h72aM3675.IsEndo (mau9h72a.E i) := by native_decide

theorem mau9h72aM4293_models : @satisfies _ (Fin 9) mau9h72aM4293 Law4293 :=
  (@Law4293.models_iff (Fin 9) mau9h72aM4293).mpr (by native_decide)

theorem mau9h72aM4293_endo : ∀ i, mau9h72aM4293.IsEndo (mau9h72a.E i) := by native_decide

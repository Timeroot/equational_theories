import equational_theories.Definability.Aut_big16h240a_data

/-! # The data lemmas for the group of order 240 on Fin 16 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace big16h240a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end big16h240a

namespace big16h240a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end big16h240a

theorem big16h240aM464_models : @satisfies _ (Fin 16) big16h240aM464 Law464 :=
  (@Law464.models_iff (Fin 16) big16h240aM464).mpr (by native_decide)

theorem big16h240aM464_endo : ∀ i, big16h240aM464.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM474_models : @satisfies _ (Fin 16) big16h240aM474 Law474 :=
  (@Law474.models_iff (Fin 16) big16h240aM474).mpr (by native_decide)

theorem big16h240aM474_endo : ∀ i, big16h240aM474.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM677_models : @satisfies _ (Fin 16) big16h240aM677 Law677 :=
  (@Law677.models_iff (Fin 16) big16h240aM677).mpr (by native_decide)

theorem big16h240aM677_endo : ∀ i, big16h240aM677.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM1076_models : @satisfies _ (Fin 16) big16h240aM1076 Law1076 :=
  (@Law1076.models_iff (Fin 16) big16h240aM1076).mpr (by native_decide)

theorem big16h240aM1076_endo : ∀ i, big16h240aM1076.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM1083_models : @satisfies _ (Fin 16) big16h240aM1083 Law1083 :=
  (@Law1083.models_iff (Fin 16) big16h240aM1083).mpr (by native_decide)

theorem big16h240aM1083_endo : ∀ i, big16h240aM1083.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM1286_models : @satisfies _ (Fin 16) big16h240aM1286 Law1286 :=
  (@Law1286.models_iff (Fin 16) big16h240aM1286).mpr (by native_decide)

theorem big16h240aM1286_endo : ∀ i, big16h240aM1286.IsEndo (big16h240a.E i) := by native_decide

theorem big16h240aM1313_models : @satisfies _ (Fin 16) big16h240aM1313 Law1313 :=
  (@Law1313.models_iff (Fin 16) big16h240aM1313).mpr (by native_decide)

theorem big16h240aM1313_endo : ∀ i, big16h240aM1313.IsEndo (big16h240a.E i) := by native_decide

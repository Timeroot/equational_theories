import equational_theories.Definability.Pat_pat36h720a_data

/-! # The data lemmas for the coordinate shuffle on Fin 36 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace pat36h720a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end pat36h720a

namespace pat36h720a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end pat36h720a

theorem pat36h720aM168_models : @satisfies _ (Fin 36) pat36h720aM168 Law168 :=
  (@Law168.models_iff (Fin 36) pat36h720aM168).mpr (by native_decide)

theorem pat36h720aM168_endo : ∀ i, pat36h720aM168.IsEndo (pat36h720a.E i) := by native_decide

theorem pat36h720aM1480_models : @satisfies _ (Fin 36) pat36h720aM1480 Law1480 :=
  (@Law1480.models_iff (Fin 36) pat36h720aM1480).mpr (by native_decide)

theorem pat36h720aM1480_endo : ∀ i, pat36h720aM1480.IsEndo (pat36h720a.E i) := by native_decide

theorem pat36h720aM1483_models : @satisfies _ (Fin 36) pat36h720aM1483 Law1483 :=
  (@Law1483.models_iff (Fin 36) pat36h720aM1483).mpr (by native_decide)

theorem pat36h720aM1483_endo : ∀ i, pat36h720aM1483.IsEndo (pat36h720a.E i) := by native_decide

theorem pat36h720aM1485_models : @satisfies _ (Fin 36) pat36h720aM1485 Law1485 :=
  (@Law1485.models_iff (Fin 36) pat36h720aM1485).mpr (by native_decide)

theorem pat36h720aM1485_endo : ∀ i, pat36h720aM1485.IsEndo (pat36h720a.E i) := by native_decide

theorem pat36h720aM1486_models : @satisfies _ (Fin 36) pat36h720aM1486 Law1486 :=
  (@Law1486.models_iff (Fin 36) pat36h720aM1486).mpr (by native_decide)

theorem pat36h720aM1486_endo : ∀ i, pat36h720aM1486.IsEndo (pat36h720a.E i) := by native_decide

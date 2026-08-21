import equational_theories.Definability.Aut_aff17h272a_data

/-! # The data lemmas for the group of order 272 on Fin 17 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aff17h272a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aff17h272a

namespace aff17h272a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aff17h272a

theorem aff17h272aM167_models : @satisfies _ (Fin 17) aff17h272aM167 Law167 :=
  (@Law167.models_iff (Fin 17) aff17h272aM167).mpr (by native_decide)

theorem aff17h272aM167_endo : ∀ i, aff17h272aM167.IsEndo (aff17h272a.E i) := by native_decide

theorem aff17h272aM1076_models : @satisfies _ (Fin 17) aff17h272aM1076 Law1076 :=
  (@Law1076.models_iff (Fin 17) aff17h272aM1076).mpr (by native_decide)

theorem aff17h272aM1076_endo : ∀ i, aff17h272aM1076.IsEndo (aff17h272a.E i) := by native_decide

theorem aff17h272aM1313_models : @satisfies _ (Fin 17) aff17h272aM1313 Law1313 :=
  (@Law1313.models_iff (Fin 17) aff17h272aM1313).mpr (by native_decide)

theorem aff17h272aM1313_endo : ∀ i, aff17h272aM1313.IsEndo (aff17h272a.E i) := by native_decide

import equational_theories.Definability.Aut_aff13h156a_data

/-! # The data lemmas for the group of order 156 on Fin 13 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aff13h156a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aff13h156a

namespace aff13h156a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aff13h156a

theorem aff13h156aM907_models : @satisfies _ (Fin 13) aff13h156aM907 Law907 :=
  (@Law907.models_iff (Fin 13) aff13h156aM907).mpr (by native_decide)

theorem aff13h156aM907_endo : ∀ i, aff13h156aM907.IsEndo (aff13h156a.E i) := by native_decide

theorem aff13h156aM1313_models : @satisfies _ (Fin 13) aff13h156aM1313 Law1313 :=
  (@Law1313.models_iff (Fin 13) aff13h156aM1313).mpr (by native_decide)

theorem aff13h156aM1313_endo : ∀ i, aff13h156aM1313.IsEndo (aff13h156a.E i) := by native_decide

theorem aff13h156aM3555_models : @satisfies _ (Fin 13) aff13h156aM3555 Law3555 :=
  (@Law3555.models_iff (Fin 13) aff13h156aM3555).mpr (by native_decide)

theorem aff13h156aM3555_endo : ∀ i, aff13h156aM3555.IsEndo (aff13h156a.E i) := by native_decide

theorem aff13h156aM4321_models : @satisfies _ (Fin 13) aff13h156aM4321 Law4321 :=
  (@Law4321.models_iff (Fin 13) aff13h156aM4321).mpr (by native_decide)

theorem aff13h156aM4321_endo : ∀ i, aff13h156aM4321.IsEndo (aff13h156a.E i) := by native_decide

theorem aff13h156aM4443_models : @satisfies _ (Fin 13) aff13h156aM4443 Law4443 :=
  (@Law4443.models_iff (Fin 13) aff13h156aM4443).mpr (by native_decide)

theorem aff13h156aM4443_endo : ∀ i, aff13h156aM4443.IsEndo (aff13h156a.E i) := by native_decide

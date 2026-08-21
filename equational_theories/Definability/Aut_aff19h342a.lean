import equational_theories.Definability.Aut_aff19h342a_data

/-! # The data lemmas for the group of order 342 on Fin 19 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aff19h342a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aff19h342a

namespace aff19h342a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aff19h342a

theorem aff19h342aM670_models : @satisfies _ (Fin 19) aff19h342aM670 Law670 :=
  (@Law670.models_iff (Fin 19) aff19h342aM670).mpr (by native_decide)

theorem aff19h342aM670_endo : ∀ i, aff19h342aM670.IsEndo (aff19h342a.E i) := by native_decide

theorem aff19h342aM907_models : @satisfies _ (Fin 19) aff19h342aM907 Law907 :=
  (@Law907.models_iff (Fin 19) aff19h342aM907).mpr (by native_decide)

theorem aff19h342aM907_endo : ∀ i, aff19h342aM907.IsEndo (aff19h342a.E i) := by native_decide

theorem aff19h342aM1076_models : @satisfies _ (Fin 19) aff19h342aM1076 Law1076 :=
  (@Law1076.models_iff (Fin 19) aff19h342aM1076).mpr (by native_decide)

theorem aff19h342aM1076_endo : ∀ i, aff19h342aM1076.IsEndo (aff19h342a.E i) := by native_decide

theorem aff19h342aM1313_models : @satisfies _ (Fin 19) aff19h342aM1313 Law1313 :=
  (@Law1313.models_iff (Fin 19) aff19h342aM1313).mpr (by native_decide)

theorem aff19h342aM1313_endo : ∀ i, aff19h342aM1313.IsEndo (aff19h342a.E i) := by native_decide

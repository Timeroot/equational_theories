import equational_theories.Definability.Aut_aut6h6a_data

/-! # The data lemmas for the group of order 6 on Fin 6 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut6h6a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h6a

namespace aut6h6a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h6a

theorem aut6h6aM1482_models : @satisfies _ (Fin 6) aut6h6aM1482 Law1482 :=
  (@Law1482.models_iff (Fin 6) aut6h6aM1482).mpr (by native_decide)

theorem aut6h6aM1482_endo : ∀ i, aut6h6aM1482.IsEndo (aut6h6a.E i) := by decide

theorem aut6h6aM3352_models : @satisfies _ (Fin 6) aut6h6aM3352 Law3352 :=
  (@Law3352.models_iff (Fin 6) aut6h6aM3352).mpr (by native_decide)

theorem aut6h6aM3352_endo : ∀ i, aut6h6aM3352.IsEndo (aut6h6a.E i) := by decide

theorem aut6h6aM3748_models : @satisfies _ (Fin 6) aut6h6aM3748 Law3748 :=
  (@Law3748.models_iff (Fin 6) aut6h6aM3748).mpr (by native_decide)

theorem aut6h6aM3748_endo : ∀ i, aut6h6aM3748.IsEndo (aut6h6a.E i) := by decide

theorem aut6h6aM4321_models : @satisfies _ (Fin 6) aut6h6aM4321 Law4321 :=
  (@Law4321.models_iff (Fin 6) aut6h6aM4321).mpr (by native_decide)

theorem aut6h6aM4321_endo : ∀ i, aut6h6aM4321.IsEndo (aut6h6a.E i) := by decide

theorem aut6h6aM4408_models : @satisfies _ (Fin 6) aut6h6aM4408 Law4408 :=
  (@Law4408.models_iff (Fin 6) aut6h6aM4408).mpr (by native_decide)

theorem aut6h6aM4408_endo : ∀ i, aut6h6aM4408.IsEndo (aut6h6a.E i) := by decide

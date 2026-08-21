import equational_theories.Definability.Aut_aut6h6b_data

/-! # The data lemmas for the group of order 6 on Fin 6 (#2) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut6h6b

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h6b

namespace aut6h6b

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h6b

theorem aut6h6bM3558_models : @satisfies _ (Fin 6) aut6h6bM3558 Law3558 :=
  (@Law3558.models_iff (Fin 6) aut6h6bM3558).mpr (by native_decide)

theorem aut6h6bM3558_endo : ∀ i, aut6h6bM3558.IsEndo (aut6h6b.E i) := by decide

theorem aut6h6bM4405_models : @satisfies _ (Fin 6) aut6h6bM4405 Law4405 :=
  (@Law4405.models_iff (Fin 6) aut6h6bM4405).mpr (by native_decide)

theorem aut6h6bM4405_endo : ∀ i, aut6h6bM4405.IsEndo (aut6h6b.E i) := by decide

theorem aut6h6bM4443_models : @satisfies _ (Fin 6) aut6h6bM4443 Law4443 :=
  (@Law4443.models_iff (Fin 6) aut6h6bM4443).mpr (by native_decide)

theorem aut6h6bM4443_endo : ∀ i, aut6h6bM4443.IsEndo (aut6h6b.E i) := by decide

import equational_theories.Definability.Aut_mau11h110a_data

/-! # The data lemmas for the group of order 110 on Fin 11 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace mau11h110a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end mau11h110a

namespace mau11h110a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end mau11h110a

theorem mau11h110aM670_models : @satisfies _ (Fin 11) mau11h110aM670 Law670 :=
  (@Law670.models_iff (Fin 11) mau11h110aM670).mpr (by native_decide)

theorem mau11h110aM670_endo : ∀ i, mau11h110aM670.IsEndo (mau11h110a.E i) := by native_decide

theorem mau11h110aM677_models : @satisfies _ (Fin 11) mau11h110aM677 Law677 :=
  (@Law677.models_iff (Fin 11) mau11h110aM677).mpr (by native_decide)

theorem mau11h110aM677_endo : ∀ i, mau11h110aM677.IsEndo (mau11h110a.E i) := by native_decide

import equational_theories.Definability.Aut_big29h406a_data

/-! # The data lemmas for the group of order 406 on Fin 29 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace big29h406a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end big29h406a

namespace big29h406a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end big29h406a

theorem big29h406aM677_models : @satisfies _ (Fin 29) big29h406aM677 Law677 :=
  (@Law677.models_iff (Fin 29) big29h406aM677).mpr (by native_decide)

theorem big29h406aM677_endo : ∀ i, big29h406aM677.IsEndo (big29h406a.E i) := by native_decide

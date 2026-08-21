import equational_theories.Definability.Aut_big47h1081a_data

/-! # The data lemmas for the group of order 1081 on Fin 47 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace big47h1081a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end big47h1081a

namespace big47h1081a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end big47h1081a

theorem big47h1081aM1685_models : @satisfies _ (Fin 47) big47h1081aM1685 Law1685 :=
  (@Law1685.models_iff (Fin 47) big47h1081aM1685).mpr (by native_decide)

theorem big47h1081aM1685_endo : ∀ i, big47h1081aM1685.IsEndo (big47h1081a.E i) := by native_decide

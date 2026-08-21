import equational_theories.Definability.Aut_big59h1711a_data

/-! # The data lemmas for the group of order 1711 on Fin 59 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace big59h1711a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end big59h1711a

namespace big59h1711a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end big59h1711a

theorem big59h1711aM1286_models : @satisfies _ (Fin 59) big59h1711aM1286 Law1286 :=
  (@Law1286.models_iff (Fin 59) big59h1711aM1286).mpr (by native_decide)

theorem big59h1711aM1286_endo : ∀ i, big59h1711aM1286.IsEndo (big59h1711a.E i) := by native_decide

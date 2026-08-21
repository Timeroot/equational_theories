import equational_theories.Definability.Aut_aut9h36a_data

/-! # The data lemmas for the group of order 36 on Fin 9 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aut9h36a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aut9h36a

namespace aut9h36a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aut9h36a

theorem aut9h36aM474_models : @satisfies _ (Fin 9) aut9h36aM474 Law474 :=
  (@Law474.models_iff (Fin 9) aut9h36aM474).mpr (by native_decide)

theorem aut9h36aM474_endo : ∀ i, aut9h36aM474.IsEndo (aut9h36a.E i) := by native_decide

theorem aut9h36aM1083_models : @satisfies _ (Fin 9) aut9h36aM1083 Law1083 :=
  (@Law1083.models_iff (Fin 9) aut9h36aM1083).mpr (by native_decide)

theorem aut9h36aM1083_endo : ∀ i, aut9h36aM1083.IsEndo (aut9h36a.E i) := by native_decide

theorem aut9h36aM1286_models : @satisfies _ (Fin 9) aut9h36aM1286 Law1286 :=
  (@Law1286.models_iff (Fin 9) aut9h36aM1286).mpr (by native_decide)

theorem aut9h36aM1286_endo : ∀ i, aut9h36aM1286.IsEndo (aut9h36a.E i) := by native_decide

theorem aut9h36aM4321_models : @satisfies _ (Fin 9) aut9h36aM4321 Law4321 :=
  (@Law4321.models_iff (Fin 9) aut9h36aM4321).mpr (by native_decide)

theorem aut9h36aM4321_endo : ∀ i, aut9h36aM4321.IsEndo (aut9h36a.E i) := by native_decide

theorem aut9h36aM4443_models : @satisfies _ (Fin 9) aut9h36aM4443 Law4443 :=
  (@Law4443.models_iff (Fin 9) aut9h36aM4443).mpr (by native_decide)

theorem aut9h36aM4443_endo : ∀ i, aut9h36aM4443.IsEndo (aut9h36a.E i) := by native_decide

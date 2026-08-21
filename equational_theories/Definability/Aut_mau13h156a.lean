import equational_theories.Definability.Aut_mau13h156a_data

/-! # The data lemmas for the group of order 156 on Fin 13 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace mau13h156a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end mau13h156a

namespace mau13h156a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end mau13h156a

theorem mau13h156aM1076_models : @satisfies _ (Fin 13) mau13h156aM1076 Law1076 :=
  (@Law1076.models_iff (Fin 13) mau13h156aM1076).mpr (by native_decide)

theorem mau13h156aM1076_endo : ∀ i, mau13h156aM1076.IsEndo (mau13h156a.E i) := by native_decide

theorem mau13h156aM1083_models : @satisfies _ (Fin 13) mau13h156aM1083 Law1083 :=
  (@Law1083.models_iff (Fin 13) mau13h156aM1083).mpr (by native_decide)

theorem mau13h156aM1083_endo : ∀ i, mau13h156aM1083.IsEndo (mau13h156a.E i) := by native_decide

theorem mau13h156aM1286_models : @satisfies _ (Fin 13) mau13h156aM1286 Law1286 :=
  (@Law1286.models_iff (Fin 13) mau13h156aM1286).mpr (by native_decide)

theorem mau13h156aM1286_endo : ∀ i, mau13h156aM1286.IsEndo (mau13h156a.E i) := by native_decide

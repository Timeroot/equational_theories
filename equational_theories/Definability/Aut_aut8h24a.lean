import equational_theories.Definability.Aut_aut8h24a_data

/-! # The data lemmas for the group of order 24 on Fin 8 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut8h24a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut8h24a

namespace aut8h24a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut8h24a

theorem aut8h24aM3272_models : @satisfies _ (Fin 8) aut8h24aM3272 Law3272 :=
  (@Law3272.models_iff (Fin 8) aut8h24aM3272).mpr (by native_decide)

theorem aut8h24aM3272_endo : ∀ i, aut8h24aM3272.IsEndo (aut8h24a.E i) := by decide

theorem aut8h24aM3748_models : @satisfies _ (Fin 8) aut8h24aM3748 Law3748 :=
  (@Law3748.models_iff (Fin 8) aut8h24aM3748).mpr (by native_decide)

theorem aut8h24aM3748_endo : ∀ i, aut8h24aM3748.IsEndo (aut8h24a.E i) := by decide

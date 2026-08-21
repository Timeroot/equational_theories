import equational_theories.Definability.Aut_aut9h18a_data

/-! # The data lemmas for the group of order 18 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut9h18a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut9h18a

namespace aut9h18a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut9h18a

theorem aut9h18aM167_models : @satisfies _ (Fin 9) aut9h18aM167 Law167 :=
  (@Law167.models_iff (Fin 9) aut9h18aM167).mpr (by native_decide)

theorem aut9h18aM167_endo : ∀ i, aut9h18aM167.IsEndo (aut9h18a.E i) := by decide

theorem aut9h18aM464_models : @satisfies _ (Fin 9) aut9h18aM464 Law464 :=
  (@Law464.models_iff (Fin 9) aut9h18aM464).mpr (by native_decide)

theorem aut9h18aM464_endo : ∀ i, aut9h18aM464.IsEndo (aut9h18a.E i) := by decide

theorem aut9h18aM1113_models : @satisfies _ (Fin 9) aut9h18aM1113 Law1113 :=
  (@Law1113.models_iff (Fin 9) aut9h18aM1113).mpr (by native_decide)

theorem aut9h18aM1113_endo : ∀ i, aut9h18aM1113.IsEndo (aut9h18a.E i) := by decide

theorem aut9h18aM3548_models : @satisfies _ (Fin 9) aut9h18aM3548 Law3548 :=
  (@Law3548.models_iff (Fin 9) aut9h18aM3548).mpr (by native_decide)

theorem aut9h18aM3548_endo : ∀ i, aut9h18aM3548.IsEndo (aut9h18a.E i) := by decide

import equational_theories.Definability.Aut_aut5h8a_data

/-! # The data lemmas for the group of order 8 on Fin 5 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut5h8a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut5h8a

namespace aut5h8a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut5h8a

theorem aut5h8aM474_models : @satisfies _ (Fin 5) aut5h8aM474 Law474 :=
  (@Law474.models_iff (Fin 5) aut5h8aM474).mpr (by native_decide)

theorem aut5h8aM474_endo : ∀ i, aut5h8aM474.IsEndo (aut5h8a.E i) := by decide

theorem aut5h8aM1685_models : @satisfies _ (Fin 5) aut5h8aM1685 Law1685 :=
  (@Law1685.models_iff (Fin 5) aut5h8aM1685).mpr (by native_decide)

theorem aut5h8aM1685_endo : ∀ i, aut5h8aM1685.IsEndo (aut5h8a.E i) := by decide

import equational_theories.Definability.Prn_prn9h8d_data

/-! # The data lemmas for the group of order 8 on Fin 9 (#4) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h8d

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h8d

namespace prn9h8d

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h8d

theorem prn9h8dM1516_models : @satisfies _ (Fin 9) prn9h8dM1516 Law1516 :=
  (@Law1516.models_iff (Fin 9) prn9h8dM1516).mpr (by native_decide)

theorem prn9h8dM1516_endo : ∀ i, prn9h8dM1516.IsEndo (prn9h8d.E i) := by decide

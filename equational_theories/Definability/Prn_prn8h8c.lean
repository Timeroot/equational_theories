import equational_theories.Definability.Prn_prn8h8c_data

/-! # The data lemmas for the group of order 8 on Fin 8 (#3) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn8h8c

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn8h8c

namespace prn8h8c

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn8h8c

theorem prn8h8cM4415_models : @satisfies _ (Fin 8) prn8h8cM4415 Law4415 :=
  (@Law4415.models_iff (Fin 8) prn8h8cM4415).mpr (by native_decide)

theorem prn8h8cM4415_endo : ∀ i, prn8h8cM4415.IsEndo (prn8h8c.E i) := by decide

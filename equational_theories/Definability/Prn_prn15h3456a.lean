import equational_theories.Definability.Prn_prn15h3456a_data

/-! # The data lemmas for the group of order 3456 on Fin 15 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace prn15h3456a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end prn15h3456a

namespace prn15h3456a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end prn15h3456a

theorem prn15h3456aM4415_models : @satisfies _ (Fin 15) prn15h3456aM4415 Law4415 :=
  (@Law4415.models_iff (Fin 15) prn15h3456aM4415).mpr (by native_decide)

theorem prn15h3456aM4415_endo : ∀ i, prn15h3456aM4415.IsEndo (prn15h3456a.E i) := by native_decide

import equational_theories.Definability.Prn_prn7h5a_data

/-! # The data lemmas for the group of order 5 on Fin 7 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn7h5a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn7h5a

namespace prn7h5a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn7h5a

theorem prn7h5aM481_models : @satisfies _ (Fin 7) prn7h5aM481 Law481 :=
  (@Law481.models_iff (Fin 7) prn7h5aM481).mpr (by native_decide)

theorem prn7h5aM481_endo : ∀ i, prn7h5aM481.IsEndo (prn7h5a.E i) := by decide

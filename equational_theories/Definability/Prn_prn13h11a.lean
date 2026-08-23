import equational_theories.Definability.Prn_prn13h11a_data

/-! # The data lemmas for the group of order 11 on Fin 13 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn13h11a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn13h11a

namespace prn13h11a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn13h11a

theorem prn13h11aM481_models : @satisfies _ (Fin 13) prn13h11aM481 Law481 :=
  (@Law481.models_iff (Fin 13) prn13h11aM481).mpr (by native_decide)

theorem prn13h11aM481_endo : ∀ i, prn13h11aM481.IsEndo (prn13h11a.E i) := by decide

import equational_theories.Definability.Aut_aut7h20a_data

/-! # The data lemmas for the group of order 20 on Fin 7 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut7h20a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut7h20a

namespace aut7h20a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut7h20a

theorem aut7h20aM1682_models : @satisfies _ (Fin 7) aut7h20aM1682 Law1682 :=
  (@Law1682.models_iff (Fin 7) aut7h20aM1682).mpr (by native_decide)

theorem aut7h20aM1682_endo : ∀ i, aut7h20aM1682.IsEndo (aut7h20a.E i) := by decide

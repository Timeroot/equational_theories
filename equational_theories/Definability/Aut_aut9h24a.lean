import equational_theories.Definability.Aut_aut9h24a_data

/-! # The data lemmas for the group of order 24 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut9h24a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut9h24a

namespace aut9h24a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut9h24a

theorem aut9h24aM3364_models : @satisfies _ (Fin 9) aut9h24aM3364 Law3364 :=
  (@Law3364.models_iff (Fin 9) aut9h24aM3364).mpr (by native_decide)

theorem aut9h24aM3364_endo : ∀ i, aut9h24aM3364.IsEndo (aut9h24a.E i) := by decide

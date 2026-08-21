import equational_theories.Definability.Aut_aut9h27a_data

/-! # The data lemmas for the group of order 27 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut9h27a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut9h27a

namespace aut9h27a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut9h27a

theorem aut9h27aM464_models : @satisfies _ (Fin 9) aut9h27aM464 Law464 :=
  (@Law464.models_iff (Fin 9) aut9h27aM464).mpr (by native_decide)

theorem aut9h27aM464_endo : ∀ i, aut9h27aM464.IsEndo (aut9h27a.E i) := by decide

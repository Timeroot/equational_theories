import equational_theories.Definability.Aut_aut6h9a_data

/-! # The data lemmas for the group of order 9 on Fin 6 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut6h9a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h9a

namespace aut6h9a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h9a

theorem aut6h9aM3355_models : @satisfies _ (Fin 6) aut6h9aM3355 Law3355 :=
  (@Law3355.models_iff (Fin 6) aut6h9aM3355).mpr (by native_decide)

theorem aut6h9aM3355_endo : ∀ i, aut6h9aM3355.IsEndo (aut6h9a.E i) := by decide

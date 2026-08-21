import equational_theories.Definability.Aut_aut6h6c_data

/-! # The data lemmas for the group of order 6 on Fin 6 (#3) -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut6h6c

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h6c

namespace aut6h6c

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h6c

theorem aut6h6cM1482_models : @satisfies _ (Fin 6) aut6h6cM1482 Law1482 :=
  (@Law1482.models_iff (Fin 6) aut6h6cM1482).mpr (by native_decide)

theorem aut6h6cM1482_endo : ∀ i, aut6h6cM1482.IsEndo (aut6h6c.E i) := by decide

theorem aut6h6cM4290_models : @satisfies _ (Fin 6) aut6h6cM4290 Law4290 :=
  (@Law4290.models_iff (Fin 6) aut6h6cM4290).mpr (by native_decide)

theorem aut6h6cM4290_endo : ∀ i, aut6h6cM4290.IsEndo (aut6h6c.E i) := by decide

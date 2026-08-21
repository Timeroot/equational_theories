import equational_theories.Definability.Aut_aff11h110a_data

/-! # The data lemmas for the group of order 110 on Fin 11 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace aff11h110a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end aff11h110a

namespace aff11h110a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end aff11h110a

theorem aff11h110aM474_models : @satisfies _ (Fin 11) aff11h110aM474 Law474 :=
  (@Law474.models_iff (Fin 11) aff11h110aM474).mpr (by native_decide)

theorem aff11h110aM474_endo : ∀ i, aff11h110aM474.IsEndo (aff11h110a.E i) := by native_decide

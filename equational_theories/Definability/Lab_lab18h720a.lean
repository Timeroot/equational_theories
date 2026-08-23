import equational_theories.Definability.Lab_lab18h720a_data

/-! # The data lemmas for the labelled shuffle on Fin 18 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace lab18h720a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end lab18h720a

namespace lab18h720a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end lab18h720a

theorem lab18h720aM3269_models : @satisfies _ (Fin 18) lab18h720aM3269 Law3269 :=
  (@Law3269.models_iff (Fin 18) lab18h720aM3269).mpr (by native_decide)

theorem lab18h720aM3269_endo : ∀ i, lab18h720aM3269.IsEndo (lab18h720a.E i) := by native_decide

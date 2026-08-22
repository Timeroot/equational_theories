import equational_theories.Definability.Prn_prn9h9a_data

/-! # The data lemmas for the group of order 9 on Fin 9 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace prn9h9a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end prn9h9a

namespace prn9h9a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end prn9h9a

theorem prn9h9aM492_models : @satisfies _ (Fin 9) prn9h9aM492 Law492 :=
  (@Law492.models_iff (Fin 9) prn9h9aM492).mpr (by native_decide)

theorem prn9h9aM492_endo : ∀ i, prn9h9aM492.IsEndo (prn9h9a.E i) := by decide

theorem prn9h9aM501_models : @satisfies _ (Fin 9) prn9h9aM501 Law501 :=
  (@Law501.models_iff (Fin 9) prn9h9aM501).mpr (by native_decide)

theorem prn9h9aM501_endo : ∀ i, prn9h9aM501.IsEndo (prn9h9a.E i) := by decide

theorem prn9h9aM3364_models : @satisfies _ (Fin 9) prn9h9aM3364 Law3364 :=
  (@Law3364.models_iff (Fin 9) prn9h9aM3364).mpr (by native_decide)

theorem prn9h9aM3364_endo : ∀ i, prn9h9aM3364.IsEndo (prn9h9a.E i) := by decide

import equational_theories.Definability.Aut_aut5h4a_data

/-! # The data lemmas for the group of order 4 on Fin 5 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace aut5h4a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut5h4a

namespace aut5h4a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut5h4a

theorem aut5h4aM115_models : @satisfies _ (Fin 5) aut5h4aM115 Law115 :=
  (@Law115.models_iff (Fin 5) aut5h4aM115).mpr (by native_decide)

theorem aut5h4aM115_endo : ∀ i, aut5h4aM115.IsEndo (aut5h4a.E i) := by decide

theorem aut5h4aM481_models : @satisfies _ (Fin 5) aut5h4aM481 Law481 :=
  (@Law481.models_iff (Fin 5) aut5h4aM481).mpr (by native_decide)

theorem aut5h4aM481_endo : ∀ i, aut5h4aM481.IsEndo (aut5h4a.E i) := by decide

theorem aut5h4aM501_models : @satisfies _ (Fin 5) aut5h4aM501 Law501 :=
  (@Law501.models_iff (Fin 5) aut5h4aM501).mpr (by native_decide)

theorem aut5h4aM501_endo : ∀ i, aut5h4aM501.IsEndo (aut5h4a.E i) := by decide

theorem aut5h4aM873_models : @satisfies _ (Fin 5) aut5h4aM873 Law873 :=
  (@Law873.models_iff (Fin 5) aut5h4aM873).mpr (by native_decide)

theorem aut5h4aM873_endo : ∀ i, aut5h4aM873.IsEndo (aut5h4a.E i) := by decide

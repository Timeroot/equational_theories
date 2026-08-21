import equational_theories.Definability.Aut_mau9h54a_data

/-! # The data lemmas for the group of order 54 on Fin 9 -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Law Law.MagmaLaw

namespace mau9h54a

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

end mau9h54a

namespace mau9h54a

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end mau9h54a

theorem mau9h54aM907_models : @satisfies _ (Fin 9) mau9h54aM907 Law907 :=
  (@Law907.models_iff (Fin 9) mau9h54aM907).mpr (by native_decide)

theorem mau9h54aM907_endo : ∀ i, mau9h54aM907.IsEndo (mau9h54a.E i) := by native_decide

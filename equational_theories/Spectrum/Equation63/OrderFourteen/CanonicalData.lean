import equational_theories.Spectrum.Equation63.OrderFourteen.RowData

/-! Every inverse and conjugacy equation in the generated row data is checked
by kernel reduction. This proves the symmetry reductions used by the proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E63.OrderFourteen.CanonicalData
theorem maps_checked : ∀ i : Fin 70,
    (∀ x, tau i (sigma i x) = x) ∧ (∀ x, sigma i (tau i x) = x) ∧
    sigma i 0 = 0 ∧
    (∀ y, sigma i (row i (tau i y)) = row (representative (target i)) y) := by
  decide +kernel

theorem chain_checked : ∀ i : Fin 21, ∀ y : Fin 14,
    (row (representative i) y).val ≤ y.val + 1 := by decide +kernel

def permutation (i : Fin 70) : Equiv.Perm (Fin 14) where
  toFun := sigma i
  invFun := tau i
  left_inv := (maps_checked i).1
  right_inv := (maps_checked i).2.1

theorem zero_fixed (i : Fin 70) : permutation i 0 = 0 := (maps_checked i).2.2.1

theorem conjugates (i : Fin 70) (y : Fin 14) :
    permutation i (row i ((permutation i).symm y)) =
      row (representative (target i)) y := (maps_checked i).2.2.2 y

end Spectrum.E63.OrderFourteen.CanonicalData

import equational_theories.Spectrum.Equation467.OrderSixteen.Canonical
import equational_theories.Spectrum.Equation467.OrderSixteen.Moves

set_option maxRecDepth 4096
namespace Spectrum.E467.OrderSixteen

def requestGood (i : Case) (r : Point × ℕ × Point) : Bool :=
  let e := move i r.1 r.2.2
  decide (r.1 < r.2.2 ∧
    (∀ x, e (axis i x) = axis i (e x)) ∧
    (∀ x, x.val < fixedCount i → e x = x) ∧
    (∀ x, ¬ (r.1.val ≤ x.val ∧ x.val < r.2.1) → e x = x) ∧ e r.2.2 = r.1)

@[spectrum_native]
theorem requests_checked : (List.finRange 67).all (fun i => (requests i).all (requestGood i)) = true := by
  native_decide

theorem request_checked (i : Case) (r : Point × ℕ × Point) (hr : r ∈ requests i) :
    r.1 < r.2.2 ∧
    (∀ x, (move i r.1 r.2.2) (axis i x) = axis i ((move i r.1 r.2.2) x)) ∧
    (∀ x, x.val < fixedCount i → (move i r.1 r.2.2) x = x) ∧
    (∀ x, ¬ (r.1.val ≤ x.val ∧ x.val < r.2.1) → (move i r.1 r.2.2) x = x) ∧
    (move i r.1 r.2.2) r.2.2 = r.1 := by
  have hi := List.all_eq_true.mp requests_checked i (List.mem_finRange _)
  have h := List.all_eq_true.mp hi r hr
  simpa only [requestGood,decide_eq_true_eq] using h

@[spectrum_native]
theorem initial_cells : ∀ i : Case,
    0 < fixedCount i ∧ (scanRow i).val < fixedCount i ∧
    ∀ y : Point, y.val < fixedCount i → cells i ⟨y.val, by omega⟩ = (scanRow i,y) := by
  native_decide

@[spectrum_native]
theorem full_data : ∀ i : Case, fullFirstUse i = true →
    isIdempotent i = false ∧
    (∀ x : Point, fixedCount i ≤ x.val → axis i x = x) ∧
    (∀ x : Point, x.val < fixedCount i → (axis i x).val < fixedCount i) ∧
    ∀ a b : Fin 256, a ≤ b →
      (cells i a).1.val < fullBound i b ∧ (cells i a).2.val < fullBound i b := by
  native_decide


end Spectrum.E467.OrderSixteen

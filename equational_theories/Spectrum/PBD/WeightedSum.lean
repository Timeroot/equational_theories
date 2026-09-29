import equational_theories.Spectrum.PBD.WeightedTransversal
import equational_theories.Spectrum.PBD.HoleIngredients

/-! A weighted TD supplies the arithmetic operation `H*t+r+a` used to
lengthen finite arithmetic progressions of constructible orders. -/
namespace Spectrum.PBD
open Classical PairDecomposition
namespace WeightedSum

theorem sum_initial {t r : ℕ} (hr : r ≤ t) :
    (∑ x : Fin t, if x.val < r then 1 else 0) = r := by
  induction t generalizing r with
  | zero =>
    have hz : r = 0 := by omega
    subst r
    simp
  | succ t ih =>
    cases r with
    | zero => simp
    | succ r =>
      simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.zero_lt_succ,ite_true,
        Fin.val_succ,Nat.add_lt_add_iff_right]
      have h := ih (r := r) (by omega)
      omega

def weights {H t : ℕ} (a r : ℕ) : Option (Option (Fin H)) → Fin t → ℕ
  | none,x => if x.val = 0 then a else 0
  | some none,x => if x.val < r then 1 else 0
  | some (some _),_ => 1

private theorem card_group {H t a r : ℕ} (ht : 0 < t) (hr : r ≤ t)
    (i : Option (Option (Fin H))) :
    Nat.card (Σ x : Fin t, Fin (weights a r i x)) =
      match i with | none => a | some none => r | some (some _) => t := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card,Nat.card_fin]
  cases i with
  | none =>
    cases t with
    | zero => omega
    | succ t => simp [weights]
  | some i =>
    cases i with
    | none => exact sum_initial hr
    | some i => simp [weights]

private theorem card_line {H t a r : ℕ} (f : Option (Option (Fin H)) → Fin t) :
    Nat.card (Σ i, Fin (weights a r i (f i))) =
      (if (f none).val = 0 then a else 0) +
      (if (f (some none)).val < r then 1 else 0) + H := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card,Nat.card_fin,Fintype.sum_option,weights,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_one,Nat.card_fin]
  omega

end WeightedSum

/-- The local weighted construction underlying Wilson's progression extension. -/
theorem DesignClosed.weighted_sum {C : Set ℕ} (hC : DesignClosed C) {H a t r : ℕ}
    (hH : H ∈ C) (hH' : H+1 ∈ C) (ha : a ∈ C)
    (hole : HasHole C a H) (hole' : HasHole C a (H+1))
    (ht : t ∈ C) (hr : r ∈ C) (htp : 0 < t) (hrt : r ≤ t)
    (D : HasTD (H+2) t) : H*t+r+a ∈ C := by
  obtain ⟨D⟩ := D
  let e : Option (Option (Fin H)) ≃ Fin (H+2) :=
    Fintype.equivFinOfCardEq (by simp [Nat.add_assoc])
  let T := D.reindex e
  let W (i : Option (Option (Fin H))) (x : Fin t) := Fin (WeightedSum.weights a r i x)
  have ingredients (p : Fin t × Fin t) :
      Nonempty (GroupDivisible C (fun i => W i (T.line p i))) := by
    have hc := WeightedSum.card_line (a := a) (r := r) (T.line p)
    by_cases hpa : (T.line p none).val = 0
    · by_cases hpr : (T.line p (some none)).val < r
      · refine ⟨GroupDivisible.ofSingleHole (Classical.choice hole') none ?_ ?_ ?_⟩
        · simp [W,WeightedSum.weights,hpa]
        · intro j hj
          cases j with
          | none => exact (hj rfl).elim
          | some j => cases j <;> simp only [W,WeightedSum.weights,hpr,ite_true] <;> infer_instance
        · simpa [W,hpa,hpr,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
      · refine ⟨GroupDivisible.ofSingleHole (Classical.choice hole) none ?_ ?_ ?_⟩
        · simp [W,WeightedSum.weights,hpa]
        · intro j hj
          cases j with
          | none => exact (hj rfl).elim
          | some j => cases j <;> simp only [W,WeightedSum.weights,hpr,ite_false] <;> infer_instance
        · simpa [W,hpa,hpr,Nat.add_comm] using hc
    · have hcard : Nat.card (Σ i, W i (T.line p i)) ∈ C := by
        by_cases hpr : (T.line p (some none)).val < r
        · change Nat.card (Σ i, Fin (WeightedSum.weights a r i (T.line p i))) ∈ C
          rw [hc]
          simpa only [hpa,hpr,ite_false,ite_true,zero_add,Nat.add_comm] using hH'
        · change Nat.card (Σ i, Fin (WeightedSum.weights a r i (T.line p i))) ∈ C
          rw [hc]
          simpa only [hpa,hpr,ite_false,zero_add] using hH
      refine ⟨GroupDivisible.ofComplete (singleBlock hcard) ?_⟩
      intro j
      cases j with
      | none => simp only [W,WeightedSum.weights,hpa,ite_false]; infer_instance
      | some j =>
        cases j with
        | none =>
          by_cases hpr : (T.line p (some none)).val < r <;>
            simp only [W,WeightedSum.weights,hpr,ite_true,ite_false] <;> infer_instance
        | some j => change Subsingleton (Fin 1); infer_instance
  let E := T.weighted W (fun p => (ingredients p).some)
  have hgroups (i : Option (Option (Fin H))) : Nat.card (Fin 0 ⊕ (Σ x, W i x)) ∈ C := by
    rw [Nat.card_sum,Nat.card_fin,zero_add]
    change Nat.card (Σ x : Fin t, Fin (WeightedSum.weights a r i x)) ∈ C
    rw [WeightedSum.card_group htp hrt]
    cases i with
    | none => exact ha
    | some i => cases i; exact hr; exact ht
  let F := E.adjoin 0 (by omega) (fun i => singleBlock (hgroups i))
  have hc : Nat.card (Fin 0 ⊕ (Σ i, Σ x, W i x)) = H*t+r+a := by
    rw [Nat.card_sum,Nat.card_fin,zero_add,Nat.card_eq_fintype_card,Fintype.card_sigma]
    simp only [Fintype.card_eq_nat_card]
    change (∑ i : Option (Option (Fin H)), Nat.card (Σ x : Fin t,
      Fin (WeightedSum.weights a r i x))) = H*t+r+a
    simp only [WeightedSum.card_group htp hrt,Fintype.sum_option,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  exact hc ▸ hC.apply F

end Spectrum.PBD

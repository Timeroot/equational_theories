import equational_theories.Spectrum.PBD.TransversalLocalization
import equational_theories.Spectrum.PBD.WeightedSum

/-! The weighted construction that transfers the complete fibre at 1 to all
fibres of a PBD-closed set (Wilson's thesis, §21.4). -/
namespace Spectrum.PBD
open Classical PairDecomposition

theorem DesignClosed.inflate_uniform {C : Set ℕ} (hC : DesignClosed C) {k n m : ℕ}
    (hk : k ∈ C) (hm : m+1 ∈ C) (hn : n ∈ designClosure {k}) (T : HasTD k m) :
    n*m+1 ∈ C := by
  obtain ⟨D⟩ := hn
  obtain ⟨T⟩ := T
  have ingredients (b : D.blocks) :
      Nonempty (GroupDivisible C (fun _ : b.val => Fin m)) := by
    have hb : Nat.card b.val = k := D.sizes _ b.property
    let e : b.val ≃ Fin k := (Finite.card_eq.mp (by simpa using hb)).some
    exact ⟨(T.reindex e).completeGroups (by rw [hb]; exact hk)⟩
  let E : GroupDivisible C (fun _ : Fin n => Fin m) := (D.inflate (fun _ => Fin m) (fun b => (ingredients b).some)).congr
    (S := fun x y => x.1 ≠ y.1) (by intro x y _; simp)
  let F := E.adjoin 1 (by omega) (fun _ => singleBlock (by simpa [Nat.add_comm] using hm))
  have h := hC.apply F
  simpa [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.add_comm] using h

namespace PeriodConstruction

def weights {H q : ℕ} (a b r : ℕ) : Option (Option (Fin H)) → Fin q → ℕ
  | none,_ => a
  | some none,x => if x.val < r then b else 0
  | some (some _),_ => b

private theorem sum_initial_weight {q r b : ℕ} (hr : r ≤ q) :
    (∑ x : Fin q, if x.val < r then b else 0) = r*b := by
  have h : (∑ x : Fin q, if x.val < r then b else 0) =
      (∑ x : Fin q, if x.val < r then 1 else 0)*b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [h,WeightedSum.sum_initial hr]

private theorem card_group {H q a b r : ℕ} (hr : r ≤ q) (i : Option (Option (Fin H))) :
    Nat.card (Σ x : Fin q, Fin (weights a b r i x)) =
      match i with | none => q*a | some none => r*b | some (some _) => q*b := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card,Nat.card_fin]
  cases i with
  | none => simp [weights]
  | some i => cases i; exact sum_initial_weight hr; simp [weights]

private theorem card_line {H q a b r : ℕ} (f : Option (Option (Fin H)) → Fin q) :
    Nat.card (Σ i, Fin (weights a b r i (f i))) =
      a+(if (f (some none)).val < r then b else 0)+H*b := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card,Nat.card_fin,Fintype.sum_option,weights,
    Finset.sum_const,Finset.card_univ,smul_eq_mul]
  omega

end PeriodConstruction

/-- The unequal-group weighted construction. -/
theorem DesignClosed.period_construction {C : Set ℕ} (hC : DesignClosed C)
    {u v r q : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) (hr : r ≤ q)
    (D₀ : Nonempty (OneGroupDesign C (u-1) (v-1) (u-1)))
    (D₁ : Nonempty (OneGroupDesign C (u-1) (v-1) u))
    (T : HasTD (u+1) q)
    (fill₀ : q*(u-1)+1 ∈ C) (fill₁ : r*(v-1)+1 ∈ C) (fill₂ : q*(v-1)+1 ∈ C) :
    (v-1)*r+(u-1)*q*v+1 ∈ C := by
  obtain ⟨T⟩ := T
  let e : Option (Option (Fin (u-1))) ≃ Fin (u+1) :=
    Fintype.equivFinOfCardEq (by simp; omega)
  let S := T.reindex e
  let W (i : Option (Option (Fin (u-1)))) (x : Fin q) :=
    Fin (PeriodConstruction.weights (u-1) (v-1) r i x)
  have ingredients (p : Fin q × Fin q) :
      Nonempty (GroupDivisible C (fun i => W i (S.line p i))) := by
    have hc := PeriodConstruction.card_line (a := u-1) (b := v-1) (r := r) (S.line p)
    have hs (j : Option (Option (Fin (u-1)))) (hj : j ≠ none) :
        Nat.card (W j (S.line p j)) = 0 ∨ Nat.card (W j (S.line p j)) = v-1 := by
      cases j with
      | none => exact (hj rfl).elim
      | some j =>
        cases j with
        | none => by_cases h : (S.line p (some none)).val < r <;> simp [W,PeriodConstruction.weights,h]
        | some j => simp [W,PeriodConstruction.weights]
    by_cases hp : (S.line p (some none)).val < r
    · refine ⟨GroupDivisible.fromOneExceptionWithZeros (Classical.choice D₁) none
        (by omega) (by omega) ?_ hs ?_⟩
      · simp [W,PeriodConstruction.weights]
      · change Nat.card (Σ i, Fin (PeriodConstruction.weights (u-1) (v-1) r i (S.line p i))) = _
        rw [hc,if_pos hp]
        nlinarith only [Nat.sub_add_cancel (by omega : 1 ≤ u)]
    · refine ⟨GroupDivisible.fromOneExceptionWithZeros (Classical.choice D₀) none
        (by omega) (by omega) ?_ hs ?_⟩
      · simp [W,PeriodConstruction.weights]
      · change Nat.card (Σ i, Fin (PeriodConstruction.weights (u-1) (v-1) r i (S.line p i))) = _
        rw [hc,if_neg hp,add_zero]
  let E := S.weighted W (fun p => (ingredients p).some)
  have hgroups (i : Option (Option (Fin (u-1)))) : Nat.card (Fin 1 ⊕ (Σ x, W i x)) ∈ C := by
    rw [Nat.card_sum,Nat.card_fin]
    change 1+Nat.card (Σ x : Fin q, Fin (PeriodConstruction.weights (u-1) (v-1) r i x)) ∈ C
    rw [PeriodConstruction.card_group hr]
    cases i with
    | none => simpa [Nat.add_comm] using fill₀
    | some i => cases i; simpa [Nat.add_comm] using fill₁; simpa [Nat.add_comm] using fill₂
  let F := E.adjoin 1 (by omega) (fun i => singleBlock (hgroups i))
  have hc : Nat.card (Fin 1 ⊕ (Σ i, Σ x, W i x)) = (v-1)*r+(u-1)*q*v+1 := by
    rw [Nat.card_sum,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_sigma]
    simp only [Fintype.card_eq_nat_card]
    change 1+(∑ i : Option (Option (Fin (u-1))), Nat.card (Σ x : Fin q,
      Fin (PeriodConstruction.weights (u-1) (v-1) r i x))) = _
    simp only [PeriodConstruction.card_group hr,Fintype.sum_option,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    have hv1 := congrArg (fun z => (u-1)*q*z) (Nat.sub_add_cancel (by omega : 1 ≤ v))
    nlinarith only [hv1]
  exact hc ▸ hC.apply F

end Spectrum.PBD

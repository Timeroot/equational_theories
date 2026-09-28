import equational_theories.Spectrum.PBD.Gluing

namespace Spectrum.PBD
open Classical

/-- k full groups and h truncated groups. At most one common point is
adjoined to the group fillings. Blocks have orders between k and k+h. -/
theorem HasTD.truncate {L : BinaryLaw} {k h q e : ℕ} (D : HasTD (k+h) q)
    (he : e ≤ 1) (r : Fin h → ℕ) (hr : ∀ j, r j ≤ q)
    (full : Nonempty (Model L (Fin (q+e))))
    (fillings : ∀ j, Nonempty (Model L (Fin (r j+e))))
    (small : ∀ n, k ≤ n → n ≤ k+h → Nonempty (Model L (Fin n))) :
    Nonempty (Model L (Fin (k*q + ∑ j, r j + e))) := by
  obtain ⟨D⟩ := D
  let T := D.reindex (finSumFinEquiv : (Fin k ⊕ Fin h) ≃ Fin (k+h))
  let A : Fin k ⊕ Fin h → Set (Fin q) := fun i => match i with
    | .inl _ => Set.univ
    | .inr j => {x | x.val < r j}
  have hc (j : Fin h) : Fintype.card (A (.inr j)) = r j := by
    let e : A (.inr j) ≃ Fin (r j) := {
      toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt (hr j)⟩,x.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    simpa using Fintype.card_congr e
  have hg (i : Fin k ⊕ Fin h) : Nonempty (Model L (Fin e ⊕ A i)) := by
    cases i with
    | inl i => exact ⟨(Classical.choice full).ofCard (by simp [A, Nat.add_comm])⟩
    | inr j => exact ⟨(Classical.choice (fillings j)).ofCard (by simp [hc, Nat.add_comm])⟩
  have hb (p : Fin q × Fin q) : Nonempty (Model L {i // T.line p i ∈ A i}) := by
    have hlo : k ≤ Fintype.card {i // T.line p i ∈ A i} := by
      let f : Fin k → {i // T.line p i ∈ A i} := fun i => ⟨.inl i,trivial⟩
      have hf : Function.Injective f := by
        intro i j hij
        exact Sum.inl.inj (congrArg Subtype.val hij)
      simpa using Fintype.card_le_of_injective f hf
    have hhi : Fintype.card {i // T.line p i ∈ A i} ≤ k+h := by
      simpa using Fintype.card_le_of_injective
        (Subtype.val : {i // T.line p i ∈ A i} → Fin k ⊕ Fin h) Subtype.val_injective
    exact ⟨(Classical.choice (small _ hlo hhi)).ofCard rfl⟩
  let M := T.glue A e he (fun i => Classical.choice (hg i)) (fun p => Classical.choice (hb p))
  have hcard : Fintype.card (Transversal.Points A e) = k*q + ∑ j, r j + e := by
    change Fintype.card (Fin e ⊕ (Σ i, A i)) = _
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma,
      Fintype.sum_sum_type]
    have hc' (i : Fin k) : Fintype.card (A (.inl i)) = q := by simp [A]
    have hn (j : Fin h) : Nat.card (A (.inr j)) = r j := by
      rw [Nat.card_eq_fintype_card]; exact hc j
    have hn' (i : Fin k) : Nat.card (A (.inl i)) = q := by
      rw [Nat.card_eq_fintype_card]; exact hc' i
    simp only [Fintype.card_eq_nat_card, hn', hn, Finset.sum_const,
      Finset.card_univ, Nat.card_fin, smul_eq_mul]
    omega
  exact ⟨M.transport (Fintype.equivFinOfCardEq hcard)⟩

theorem HasTD.oneHole {L : BinaryLaw} {k q r e : ℕ} (D : HasTD (k+1) q)
    (he : e ≤ 1) (hr : r ≤ q) (full : Nonempty (Model L (Fin (q+e))))
    (part : Nonempty (Model L (Fin (r+e))))
    (small : ∀ n, k ≤ n → n ≤ k+1 → Nonempty (Model L (Fin n))) :
    Nonempty (Model L (Fin (k*q+r+e))) := by
  simpa using D.truncate he (fun _ => r) (fun _ => hr) full (fun _ => part) small

theorem HasTD.twoHoles {L : BinaryLaw} {k q r s e : ℕ} (D : HasTD (k+2) q)
    (he : e ≤ 1) (hr : r ≤ q) (hs : s ≤ q) (full : Nonempty (Model L (Fin (q+e))))
    (R : Nonempty (Model L (Fin (r+e)))) (S : Nonempty (Model L (Fin (s+e))))
    (small : ∀ n, k ≤ n → n ≤ k+2 → Nonempty (Model L (Fin n))) :
    Nonempty (Model L (Fin (k*q+r+s+e))) := by
  have h := D.truncate he ![r,s] (by intro j; fin_cases j; exact hr; exact hs)
    full (by intro j; fin_cases j; exact R; exact S) small
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using h

end Spectrum.PBD

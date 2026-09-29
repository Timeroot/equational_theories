import equational_theories.Spectrum.PBD.Closure
import equational_theories.Spectrum.PBD.Gluing

/-! Transversal designs as pair decompositions, and truncation in PBD closure. -/
namespace Spectrum.PBD
open Classical PairDecomposition
namespace Transversal
variable {K : Set ℕ} {I Q : Type*} [Finite Q]

def truncatedLineEquiv (D : Transversal I Q) (A : I → Set Q) (p : Q × Q) :
    {x : Σ i, A i | x.2.val = D.line p x.1} ≃ {i | D.line p i ∈ A i} where
  toFun x := ⟨x.val.1,(congrArg (fun q => q ∈ A x.val.1) x.property).mp x.val.2.property⟩
  invFun i := ⟨⟨i.val,⟨D.line p i.val,i.property⟩⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact point_eq A rfl x.property.symm
  right_inv _ := rfl

noncomputable def truncated (D : Transversal I Q) (A : I → Set Q)
    (sizes : ∀ p, Nat.card {i | D.line p i ∈ A i} ∈ K) :
    GroupDivisible K (fun i => A i) := by
  apply ofIndexed (fun p : Q × Q => {x : Σ i, A i | x.2.val = D.line p x.1})
  · intro p
    rw [Nat.card_congr (truncatedLineEquiv D A p)]
    exact sizes p
  · intro p x hx y hy hxy hi
    exact hxy (point_eq A hi (hx.trans ((congrArg (D.line p) hi).trans hy.symm)))
  · intro x y _ hij
    obtain ⟨p,hp⟩ := (D.pair x.1 y.1 hij).surjective (x.2.val,y.2.val)
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    refine ⟨p,⟨hx.symm,hy.symm⟩,?_⟩
    intro q hq
    apply (D.pair x.1 y.1 hij).injective
    exact Prod.ext (hq.1.symm.trans hx.symm) (hq.2.symm.trans hy.symm)

noncomputable def completeGroups (D : Transversal I Q) [Finite I]
    (hI : Nat.card I ∈ K) : GroupDivisible K (fun _ : I => Q) := by
  let E := D.truncated (fun _ => Set.univ) (by intro p; simpa using hI)
  exact (E.transport (Equiv.sigmaCongrRight (fun _ => Equiv.Set.univ Q))).congr
    (by intro x y _; rfl)
end Transversal

/-- PBD version of the general truncated-transversal construction. -/
theorem DesignClosed.truncate {K : Set ℕ} (hK : DesignClosed K)
    {k h q e : ℕ} (D : HasTD (k+h) q) (he : e ≤ 1)
    (r : Fin h → ℕ) (hr : ∀ j, r j ≤ q)
    (full : q+e ∈ K) (fillings : ∀ j, r j+e ∈ K)
    (small : ∀ n, k ≤ n → n ≤ k+h → n ∈ K) :
    k*q + ∑ j, r j + e ∈ K := by
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
  have hb (p : Fin q × Fin q) : Nat.card {i | T.line p i ∈ A i} ∈ K := by
    have hlo : k ≤ Fintype.card {i | T.line p i ∈ A i} := by
      let f : Fin k → {i | T.line p i ∈ A i} := fun i => ⟨.inl i,trivial⟩
      have hf : Function.Injective f := by
        intro i j hij
        exact Sum.inl.inj (congrArg Subtype.val hij)
      simpa using Fintype.card_le_of_injective f hf
    have hhi : Fintype.card {i | T.line p i ∈ A i} ≤ k+h := by
      simpa using Fintype.card_le_of_injective
        (Subtype.val : {i | T.line p i ∈ A i} → Fin k ⊕ Fin h) Subtype.val_injective
    exact small _ (by simpa using hlo) (by simpa using hhi)
  let E := T.truncated A hb
  have hg (i : Fin k ⊕ Fin h) : Nat.card (Fin e ⊕ A i) ∈ K := by
    cases i with
    | inl i => simpa [Nat.card_eq_fintype_card,A,Nat.add_comm] using full
    | inr j => simpa [Nat.card_eq_fintype_card,hc,Nat.add_comm] using fillings j
  have hcard : Nat.card (Fin e ⊕ (Σ i, A i)) = k*q + ∑ j, r j + e := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin,
      Fintype.card_sigma,Fintype.sum_sum_type]
    have hc' (i : Fin k) : Fintype.card (A (.inl i)) = q := by simp [A]
    simp only [← Nat.card_eq_fintype_card] at hc hc'
    simp only [Fintype.card_eq_nat_card,hc',hc,Finset.sum_const,Finset.card_univ,
      Nat.card_fin,smul_eq_mul]
    omega
  rw [← hcard]
  exact hK.apply (E.adjoin e he (fun i => singleBlock (hg i)))

theorem DesignClosed.oneHole {K : Set ℕ} (hK : DesignClosed K)
    {k q r e : ℕ} (D : HasTD (k+1) q) (he : e ≤ 1) (hr : r ≤ q)
    (full : q+e ∈ K) (part : r+e ∈ K) (hk : k ∈ K) (hk' : k+1 ∈ K) :
    k*q+r+e ∈ K := by
  simpa using hK.truncate D he (fun _ => r) (fun _ => hr) full (fun _ => part)
    (fun n hlo hhi => by
      have : n = k ∨ n = k+1 := by omega
      rcases this with rfl | rfl <;> assumption)

end Spectrum.PBD

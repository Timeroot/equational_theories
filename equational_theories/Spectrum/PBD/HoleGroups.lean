import equational_theories.Spectrum.PBD.Hole

/-! Regard a hole as one large group, with all remaining groups singletons. -/
namespace Spectrum.PBD
open Classical PairDecomposition
namespace PairDecomposition.GroupDivisible
variable {K : Set ℕ} {I : Type*} {A : I → Type*}

theorem pair_ne_of_subsingleton (hA : ∀ i, Subsingleton (A i))
    {x y : Σ i, A i} (hxy : x ≠ y) : x.1 ≠ y.1 := by
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  intro h
  dsimp at h
  subst j
  exact hxy (congrArg (Sigma.mk i) (@Subsingleton.elim _ (hA i) x y))

noncomputable def ofComplete (D : Complete K (Σ i, A i)) (hA : ∀ i, Subsingleton (A i)) :
    GroupDivisible K A :=
  D.congr (fun _ _ hxy => ⟨fun _ => pair_ne_of_subsingleton hA hxy,fun _ => trivial⟩)

def groupFibreEquiv (i : I) : {x : Σ i, A i | x.1 = i} ≃ A i where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv x := by rcases x with ⟨⟨j,x⟩,h⟩; dsimp at h; subst j; rfl
  right_inv _ := rfl

/-- All groups except one may be empty or singleton. Their union supplies
exactly the points outside a single hole. -/
noncomputable def ofSingleHole [Finite I] [∀ i, Finite (A i)]
    {a v : ℕ} (D : HoleDesign K (Fin a) (Fin v)) (i : I)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Subsingleton (A j))
    (hc : Nat.card (Σ j, A j) = a+v) : GroupDivisible K A := by
  let U : Set (Σ j, A j) := {x | x.1 = i}
  have hU : Nat.card U = a := (Nat.card_congr (groupFibreEquiv (A := A) i)).trans hi
  have hUc : Nat.card (Uᶜ : Set (Σ j, A j)) = v := by
    have ht : Nat.card U + Nat.card (Uᶜ : Set (Σ j, A j)) = Nat.card (Σ j, A j) := by
      rw [← Nat.card_sum,Nat.card_congr (Equiv.Set.sumCompl U)]
    omega
  let eu : U ≃ Fin a := (Finite.card_eq.mp (by simpa using hU)).some
  let ev : (Uᶜ : Set (Σ j, A j)) ≃ Fin v := (Finite.card_eq.mp (by simpa using hUc)).some
  let e : (Σ j, A j) ≃ Fin a ⊕ Fin v := (Equiv.Set.sumCompl U).symm.trans (Equiv.sumCongr eu ev)
  have he (x : Σ j, A j) : (e x).isLeft ↔ x.1 = i := by
    by_cases hx : x ∈ U
    · simp [e,Equiv.Set.sumCompl_symm_apply_of_mem hx,show x.1 = i from hx]
    · simp [e,Equiv.Set.sumCompl_symm_apply_of_notMem hx,show x.1 ≠ i from hx]
  apply (D.transport e.symm).congr
  intro x y hxy
  change ¬((e x).isLeft ∧ (e y).isLeft) ↔ x.1 ≠ y.1
  rw [he,he]
  constructor
  · intro h heq
    have hx : x.1 ≠ i := fun hx => h ⟨hx,heq.symm.trans hx⟩
    rcases x with ⟨j,x⟩
    rcases y with ⟨l,y⟩
    dsimp at heq hx
    subst l
    exact hxy (congrArg (Sigma.mk j) (@Subsingleton.elim _ (hs j hx) x y))
  · rintro h ⟨hx,hy⟩
    exact h (hx.trans hy.symm)

end PairDecomposition.GroupDivisible
end Spectrum.PBD

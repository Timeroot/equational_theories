import equational_theories.Spectrum.Idempotent1489
import equational_theories.Spectrum.TransversalSeven

/-! Truncate two groups of a transversal design and glue idempotent E1489 models. -/
open Classical
namespace Spectrum.TransversalSeven

variable {Q : Type*} (D : TransversalSeven Q) (A : Fin 7 → Set Q)

abbrev Points := Σ i : Fin 7, A i

def block : Fin 7 ⊕ (Q × Q) → Set (Points A)
  | .inl i => {x | x.1 = i}
  | .inr p => {x | x.2.val = D.line p x.1}

theorem point_eq {x y : Points A} (hi : x.1 = y.1) (hv : x.2.val = y.2.val) : x = y := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  dsimp at hi hv
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hv)

theorem cover (x y : Points A) (hxy : x ≠ y) :
    ∃! b, x ∈ block D A b ∧ y ∈ block D A b := by
  by_cases hi : x.1 = y.1
  · refine ⟨.inl x.1, ⟨rfl,hi.symm⟩, ?_⟩
    intro b hb
    cases b with
    | inl i => exact congrArg Sum.inl hb.1.symm
    | inr p =>
      exact (hxy (point_eq A hi (hb.1.trans ((congrArg (D.line p) hi).trans hb.2.symm)))).elim
  · obtain ⟨p,hp⟩ := (D.pair x.1 y.1 hi).surjective (x.2.val,y.2.val)
    obtain ⟨hx,hy⟩ := Prod.mk.inj hp
    refine ⟨.inr p, ⟨hx.symm,hy.symm⟩, ?_⟩
    intro b hb
    cases b with
    | inl i => exact (hi (hb.1.trans hb.2.symm)).elim
    | inr q =>
      apply congrArg Sum.inr
      apply (D.pair x.1 y.1 hi).injective
      exact Prod.ext (hb.1.symm.trans hx.symm) (hb.2.symm.trans hy.symm)

def groupEquiv (i : Fin 7) : block D A (.inl i) ≃ A i where
  toFun x := ⟨x.val.2.val,
    (congrArg (fun j => x.val.2.val ∈ A j) x.property).mp x.val.2.property⟩
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact point_eq A x.property.symm rfl
  right_inv x := rfl

theorem line_card [Fintype Q]
    (hfull : ∀ i : Fin 7, i.val < 5 → A i = Set.univ) (p : Q × Q) :
    5 ≤ Fintype.card (block D A (.inr p)) ∧ Fintype.card (block D A (.inr p)) ≤ 7 := by
  let f : block D A (.inr p) → Fin 7 := fun x => x.val.1
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply point_eq A h
    exact x.property.trans ((congrArg (D.line p) h).trans y.property.symm)
  let g : Fin 5 → block D A (.inr p) := fun i =>
    ⟨⟨i.castLE (by omega), ⟨D.line p (i.castLE (by omega)), by
      rw [hfull _ i.isLt]; trivial⟩⟩,rfl⟩
  have hg : Function.Injective g := by
    intro i j h
    have he := congrArg (fun x => x.val.1.val) h
    exact Fin.ext he
  exact ⟨by simpa using Fintype.card_le_of_injective g hg,
    by simpa using Fintype.card_le_of_injective f hf⟩

noncomputable def glued [Fintype Q]
    (hfull : ∀ i : Fin 7, i.val < 5 → A i = Set.univ)
    (groups : ∀ i, Idempotent1489 (A i))
    (small : ∀ n : ℕ, 5 ≤ n → n ≤ 7 → Nonempty (Idempotent1489 (Fin n))) :
    Idempotent1489 (Points A) := by
  apply Idempotent1489.glue (block D A) _ (cover D A)
  intro b
  cases b with
  | inl i => exact (groups i).transport (groupEquiv D A i)
  | inr p =>
    have hc := line_card D A hfull p
    let M := Classical.choice (small _ hc.1 hc.2)
    exact Idempotent1489.ofCard rfl M

include D in
theorem model_interval [Fintype Q] {r s : ℕ}
    (hr : r ≤ Fintype.card Q) (hs : s ≤ Fintype.card Q)
    (M : Idempotent1489 (Fin (Fintype.card Q)))
    (R : Idempotent1489 (Fin r)) (S : Idempotent1489 (Fin s))
    (small : ∀ n : ℕ, 5 ≤ n → n ≤ 7 → Nonempty (Idempotent1489 (Fin n))) :
    Nonempty (Idempotent1489 (Fin (5 * Fintype.card Q + r + s))) := by
  obtain ⟨U,_,hU⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Q)) (by simpa using hr)
  obtain ⟨V,_,hV⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Q)) (by simpa using hs)
  let A : Fin 7 → Set Q := ![Set.univ,Set.univ,Set.univ,Set.univ,Set.univ,↑U,↑V]
  have hfull : ∀ i : Fin 7, i.val < 5 → A i = Set.univ := by
    intro i hi
    fin_cases i <;> simp_all [A]
  have hgroups : ∀ i, Nonempty (Idempotent1489 (A i)) := by
    intro i
    fin_cases i
    · exact ⟨Idempotent1489.ofCard (by simp [A]) M⟩
    · exact ⟨Idempotent1489.ofCard (by simp [A]) M⟩
    · exact ⟨Idempotent1489.ofCard (by simp [A]) M⟩
    · exact ⟨Idempotent1489.ofCard (by simp [A]) M⟩
    · exact ⟨Idempotent1489.ofCard (by simp [A]) M⟩
    · exact ⟨Idempotent1489.ofCard (by simpa [A] using hU) R⟩
    · exact ⟨Idempotent1489.ofCard (by simpa [A] using hV) S⟩
  have hc : Fintype.card (Points A) = 5 * Fintype.card Q + r + s := by
    simp [Points, Fintype.card_sigma, Fin.sum_univ_succ, A, hU, hV]
    omega
  exact ⟨(glued D A hfull (fun i => Classical.choice (hgroups i)) small).transport
    (Fintype.equivFinOfCardEq hc).symm⟩

end Spectrum.TransversalSeven

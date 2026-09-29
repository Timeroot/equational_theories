import equational_theories.Spectrum.PBD.Fundamental

/-! Fill the groups of a GDD, optionally adjoining a common point. -/
namespace Spectrum.PBD.PairDecomposition
open Classical
variable {K : Set ℕ} {I : Type*} {A : I → Type*}

namespace GroupDivisible
variable (D : GroupDivisible K A) (e : ℕ)

abbrev AdjoinPoints := Fin e ⊕ (Σ i, A i)

def adjoinBlock : I ⊕ D.blocks → Set (AdjoinPoints (A := A) e)
  | .inl i => fun x => match x with
    | .inl _ => True
    | .inr x => x.1 = i
  | .inr b => fun x => match x with
    | .inl _ => False
    | .inr x => x ∈ b.val

def adjoinGroupEquiv (i : I) : adjoinBlock D e (.inl i) ≃ Fin e ⊕ A i where
  toFun x := match x with
    | ⟨.inl x,_⟩ => .inl x
    | ⟨.inr ⟨j,x⟩,h⟩ => .inr (h ▸ x)
  invFun x := match x with
    | .inl x => ⟨.inl x,trivial⟩
    | .inr x => ⟨.inr ⟨i,x⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨x,h⟩
    cases x with
    | inl x => rfl
    | inr x =>
      rcases x with ⟨j,x⟩
      change j = i at h
      subst j
      rfl
  right_inv x := by cases x <;> rfl

def adjoinLineEquiv (b : D.blocks) : adjoinBlock D e (.inr b) ≃ b.val where
  toFun x := match x with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr x,h⟩ => ⟨x,h⟩
  invFun x := ⟨.inr x.val,x.property⟩
  left_inv x := by
    rcases x with ⟨x,h⟩
    cases x with
    | inl _ => exact h.elim
    | inr _ => rfl
  right_inv _ := rfl

theorem adjoinCover (he : e ≤ 1) (x y : AdjoinPoints (A := A) e) (hxy : x ≠ y) :
    ∃! b, x ∈ adjoinBlock D e b ∧ y ∈ adjoinBlock D e b := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact (hxy (congrArg Sum.inl (Fin.ext (by omega)))).elim
    | inr y =>
      refine ⟨.inl y.1, ⟨trivial,rfl⟩, ?_⟩
      intro b hb
      cases b with
      | inl i => exact congrArg Sum.inl hb.2.symm
      | inr b => exact hb.1.elim
  | inr x =>
    cases y with
    | inl y =>
      refine ⟨.inl x.1, ⟨rfl,trivial⟩, ?_⟩
      intro b hb
      cases b with
      | inl i => exact congrArg Sum.inl hb.1.symm
      | inr b => exact hb.2.elim
    | inr y =>
      have hxy' : x ≠ y := fun h => hxy (congrArg Sum.inr h)
      by_cases hi : x.1 = y.1
      · refine ⟨.inl x.1, ⟨rfl,hi.symm⟩, ?_⟩
        intro b hb
        cases b with
        | inl i => exact congrArg Sum.inl hb.1.symm
        | inr b => exact ((D.sound _ b.property _ hb.1 _ hb.2 hxy') hi).elim
      · obtain ⟨b,hb,hu⟩ := D.cover x y hxy' hi
        refine ⟨.inr b,hb,?_⟩
        intro c hc
        cases c with
        | inl i => exact (hi (hc.1.trans hc.2.symm)).elim
        | inr c => exact congrArg Sum.inr (hu c hc)


noncomputable def adjoinIngredient (groups : ∀ i, Complete K (Fin e ⊕ A i)) :
    ∀ b, Complete K (adjoinBlock D e b)
  | .inl i => (groups i).transport (adjoinGroupEquiv D e i).symm
  | .inr b => singleBlock (by
      rw [Nat.card_congr (adjoinLineEquiv D e b)]
      exact D.sizes _ b.property)

/-- Adjoin zero or one common point and fill the enlarged groups. -/
noncomputable def adjoin [Finite I] (he : e ≤ 1)
    (groups : ∀ i, Complete K (Fin e ⊕ A i)) : Complete K (AdjoinPoints (A := A) e) :=
  assemble (adjoinBlock D e) (adjoinCover D e he) (adjoinIngredient D e groups)

theorem adjoin_contains_group [Finite I] (he : e ≤ 1)
    (groups : ∀ i, Complete K (Fin e ⊕ A i)) (i : I) {s : ℕ}
    (h : (groups i).ContainsBlock s) : (D.adjoin e he groups).ContainsBlock s := by
  apply assemble_contains (adjoinBlock D e) (adjoinCover D e he)
    (adjoinIngredient D e groups) (.inl i)
  exact h.transport (adjoinGroupEquiv D e i).symm

theorem adjoin_contains_line [Finite I] (he : e ≤ 1)
    (groups : ∀ i, Complete K (Fin e ⊕ A i)) (b : D.blocks) :
    (D.adjoin e he groups).ContainsBlock (Nat.card b.val) := by
  apply assemble_contains (adjoinBlock D e) (adjoinCover D e he)
    (adjoinIngredient D e groups) (.inr b)
  have h := singleBlock_contains (K := K) (X := adjoinBlock D e (.inr b))
    ((Nat.card_congr (adjoinLineEquiv D e b)).symm ▸ D.sizes _ b.property)
  simpa only [Nat.card_congr (adjoinLineEquiv D e b)] using h

end GroupDivisible
end Spectrum.PBD.PairDecomposition

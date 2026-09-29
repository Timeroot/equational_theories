import equational_theories.Spectrum.PBD.Replication

/-! Incomplete designs: delete a block and retain a single unfilled hole. -/
namespace Spectrum.PBD
open Classical PairDecomposition

namespace PairDecomposition
variable {K : Set ℕ} {X : Type*}

noncomputable def deleteBlock (D : Complete K X) (b : D.blocks) :
    PairDecomposition K X (fun x y => ¬(x ∈ b.val ∧ y ∈ b.val)) := by
  apply ofIndexed (fun c : {c : D.blocks // c ≠ b} => c.val.val)
  · intro c
    exact D.sizes _ c.val.property
  · intro c x hx y hy hxy hb
    exact c.property ((D.cover x y hxy trivial).unique ⟨hx,hy⟩ hb)
  · intro x y hxy hb
    obtain ⟨c,hc,hu⟩ := D.cover x y hxy trivial
    have hcb : c ≠ b := fun h => hb (h ▸ hc)
    refine ⟨⟨c,hcb⟩,hc,?_⟩
    intro d hd
    exact Subtype.ext (hu d.val hd)

end PairDecomposition

abbrev HoleDesign (K : Set ℕ) (U X : Type*) :=
  PairDecomposition K (U ⊕ X) (fun x y => ¬(x.isLeft ∧ y.isLeft))

def HasHole (K : Set ℕ) (a v : ℕ) : Prop := Nonempty (HoleDesign K (Fin a) (Fin v))

namespace HoleDesign
variable {K : Set ℕ} {U X V Y : Type*}

noncomputable def relabel (D : HoleDesign K U X) (e : U ≃ V) (f : X ≃ Y) :
    HoleDesign K V Y := by
  apply (D.transport (Equiv.sumCongr e f)).congr
  intro x y _
  cases x <;> cases y <;> rfl

noncomputable def ofCards [Finite U] [Finite X] (D : HoleDesign K U X)
    {a v : ℕ} (hU : Nat.card U = a) (hX : Nat.card X = v) :
    HoleDesign K (Fin a) (Fin v) :=
  D.relabel (Finite.card_eq.mp (by simpa using hU)).some
    (Finite.card_eq.mp (by simpa using hX)).some

end HoleDesign

/-- Deleting a designated block leaves a hole of that size. -/
theorem PairDecomposition.ContainsBlock.hole {K : Set ℕ} {X : Type*} [Finite X]
    {D : Complete K X} {a v : ℕ} (h : D.ContainsBlock a) (hc : Nat.card X = a+v) :
    HasHole K a v := by
  obtain ⟨b,hb,hs⟩ := h
  let e : X ≃ b ⊕ (bᶜ : Set X) := (Equiv.Set.sumCompl b).symm
  let E : HoleDesign K b (bᶜ : Set X) := ((D.deleteBlock ⟨b,hb⟩).transport e).congr (by
    intro x y _
    cases x with
    | inl x =>
      cases y with
      | inl y => simp [e,x.property,y.property]
      | inr y => simp [e,x.property,show y.val ∉ b from y.property]
    | inr x =>
      cases y with
      | inl y => simp [e,show x.val ∉ b from x.property,y.property]
      | inr y => simp [e,show x.val ∉ b from x.property])
  have ht : Nat.card b + Nat.card (bᶜ : Set X) = Nat.card X := by
    rw [← Nat.card_sum,Nat.card_congr (Equiv.Set.sumCompl b)]
  exact ⟨E.ofCards hs (by omega)⟩

namespace HasHole
variable {K : Set ℕ} {a v : ℕ}

/-- Complete designs are holes of size zero. -/
theorem zero (h : v ∈ designClosure K) : HasHole K 0 v := by
  obtain ⟨D⟩ := h
  let e : Fin v ≃ Fin 0 ⊕ Fin v := (Equiv.emptySum (Fin 0) (Fin v)).symm
  refine ⟨(D.transport e).congr ?_⟩
  intro x y _
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x => cases y <;> simp

/-- A singleton hole has no pairs to remove. -/
theorem one (h : v+1 ∈ designClosure K) : HasHole K 1 v := by
  obtain ⟨D⟩ := h
  let e : Fin (v+1) ≃ Fin 1 ⊕ Fin v :=
    (Fintype.equivFinOfCardEq (by simp [Nat.add_comm])).symm
  refine ⟨(D.transport e).congr ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact (hxy (congrArg Sum.inl (Subsingleton.elim _ _))).elim
    | inr y => simp
  | inr x => cases y <;> simp

end HasHole
end Spectrum.PBD

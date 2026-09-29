import equational_theories.Spectrum.PBD.Closure

/-! Localize a PBD at one point: the blocks through that point become groups,
with the point removed, and all other blocks remain blocks of a GDD. -/
namespace Spectrum.PBD.PairDecomposition
open Classical
variable {K : Set ℕ} {X : Type*} (D : Complete K X) (o : X)

abbrev LocalGroups := {b : D.blocks // o ∈ b.val}
abbrev LocalGroup (b : LocalGroups D o) := {x : X // x ∈ b.val.val ∧ x ≠ o}
abbrev AwayBlocks := {b : D.blocks // o ∉ b.val}

noncomputable def localGroupOf (x : {x : X // x ≠ o}) : LocalGroups D o :=
  ⟨(D.cover o x.val x.property.symm trivial).exists.choose,
    (D.cover o x.val x.property.symm trivial).exists.choose_spec.1⟩

theorem mem_localGroupOf (x : {x : X // x ≠ o}) : x.val ∈ (localGroupOf D o x).val.val :=
  (D.cover o x.val x.property.symm trivial).exists.choose_spec.2

theorem localGroup_unique {x : X} (hx : x ≠ o) (b c : LocalGroups D o)
    (hb : x ∈ b.val.val) (hc : x ∈ c.val.val) : b = c := by
  apply Subtype.ext
  exact (D.cover o x hx.symm trivial).unique ⟨b.property,hb⟩ ⟨c.property,hc⟩

noncomputable def localizationEquiv : (Σ b : LocalGroups D o, LocalGroup D o b) ≃ {x : X // x ≠ o} where
  toFun x := ⟨x.2.val,x.2.property.2⟩
  invFun x := ⟨localGroupOf D o x,⟨x.val,mem_localGroupOf D o x,x.property⟩⟩
  left_inv x := by
    rcases x with ⟨b,x⟩
    have hb : localGroupOf D o ⟨x.val,x.property.2⟩ = b :=
      localGroup_unique D o x.property.2 _ b (mem_localGroupOf D o _) x.property.1
    apply Sigma.ext hb
    exact (Subtype.heq_iff_coe_eq (by intro z; dsimp; rw [hb])).mpr rfl
  right_inv _ := rfl

def localBlock (b : AwayBlocks D o) : Set (Σ i : LocalGroups D o, LocalGroup D o i) :=
  {x | x.2.val ∈ b.val.val}

noncomputable def localBlockEquiv (b : AwayBlocks D o) : localBlock D o b ≃ b.val.val where
  toFun x := ⟨x.val.2.val,x.property⟩
  invFun x := ⟨(localizationEquiv D o).symm ⟨x.val,fun h => b.property ((congrArg (fun y => y ∈ b.val.val) h).mp x.property)⟩,x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply (localizationEquiv D o).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  right_inv _ := rfl

/-- Deleting one point from a PBD gives a group-divisible design. -/
noncomputable def localize : GroupDivisible K (LocalGroup D o) := by
  apply ofIndexed (localBlock D o)
  · intro b
    rw [Nat.card_congr (localBlockEquiv D o b)]
    exact D.sizes _ b.val.property
  · intro b x hx y hy hxy hi
    have hval : x.2.val ≠ y.2.val := by
      intro h
      apply hxy
      apply (localizationEquiv D o).injective
      exact Subtype.ext h
    have hb : b.val = x.1.val := (D.cover _ _ hval trivial).unique
      ⟨hx,hy⟩ ⟨x.2.property.1,by simpa [hi] using y.2.property.1⟩
    exact b.property (hb ▸ x.1.property)
  · intro x y _ hij
    have hval : x.2.val ≠ y.2.val := by
      intro h
      exact hij (localGroup_unique D o x.2.property.2 _ _ x.2.property.1
        (h ▸ y.2.property.1))
    obtain ⟨b,hb,hu⟩ := D.cover x.2.val y.2.val hval trivial
    have hbo : o ∉ b.val := by
      intro ho
      have hx := localGroup_unique D o x.2.property.2 x.1 ⟨b,ho⟩ x.2.property.1 hb.1
      have hy := localGroup_unique D o y.2.property.2 y.1 ⟨b,ho⟩ y.2.property.1 hb.2
      exact hij (hx.trans hy.symm)
    refine ⟨⟨b,hbo⟩,hb,?_⟩
    intro c hc
    exact Subtype.ext (hu c.val hc)

/-- Each localized group has one fewer point than its original block. -/
theorem card_localGroup [Finite X] (b : LocalGroups D o) :
    Nat.card (LocalGroup D o b) = Nat.card b.val.val - 1 := by
  letI := Fintype.ofFinite X
  let e : LocalGroup D o b ≃ {x : b.val.val // x ≠ ⟨o,b.property⟩} := {
    toFun := fun x => ⟨⟨x.val,x.property.1⟩,fun h => x.property.2 (congrArg Subtype.val h)⟩
    invFun := fun x => ⟨x.val.val,x.val.property,fun h => x.property (Subtype.ext h)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

theorem card_localPoints [Finite X] :
    Nat.card (Σ b : LocalGroups D o, LocalGroup D o b) = Nat.card X - 1 := by
  letI := Fintype.ofFinite X
  rw [Nat.card_congr (localizationEquiv D o),Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

end Spectrum.PBD.PairDecomposition

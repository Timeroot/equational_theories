import equational_theories.Spectrum.Equation667CommutativeBlocks
import Mathlib.Data.Fintype.BigOperators
import equational_theories.Spectrum.Equation667Subclasses

/-! The five-element subalgebras of a finite commutative idempotent E667
magma form a 2-(n,5,1) design. -/
namespace Spectrum.E667.CommutativeDesign
open Classical
variable {Q : Type*} [Magma Q]

abbrev Closed (S : Finset Q) : Prop := ∀ x ∈ S, ∀ y ∈ S, x ◇ y ∈ S
abbrev Block (Q : Type*) [Magma Q] := {S : Finset Q // S.card = 5 ∧ Closed S}

/-- Two prescribed points generate the entire five-point mean algebra. -/
theorem generated (f : ZMod 5 → Q)
    (hf : ∀ i j, f (BinaryFive.base i j) = f i ◇ f j)
    (S : Finset Q) (hS : Closed S) (h0 : f 0 ∈ S) (h1 : f 1 ∈ S) :
    ∀ i, f i ∈ S := by
  have h3 : f 3 ∈ S := by
    have hh := hS _ h0 _ h1
    rw [← hf] at hh
    exact hh
  have h4 : f 4 ∈ S := by
    have hh := hS _ h0 _ h3
    rw [← hf] at hh
    exact hh
  have h2 : f 2 ∈ S := by
    have hh := hS _ h0 _ h4
    rw [← hf] at hh
    exact hh
  intro i
  fin_cases i <;> assumption

variable [Finite Q] (h : Equation667 Q)
    (hc : ∀ x y : Q, x ◇ y = y ◇ x) (hi : ∀ x : Q, x ◇ x = x)
include h hc hi

/-- The blocks are intrinsic: precisely the five-element subalgebras. -/
theorem cover (a b : Q) (hab : a ≠ b) :
    ∃! S : Block Q, a ∈ S.val ∧ b ∈ S.val := by
  obtain ⟨f, hf0, hf1, hf⟩ := CommutativeBlocks.five_embedding h hc hi a b hab
  let S := Finset.univ.map f
  have hcard : S.card = 5 := by simp [S]
  have hclosed : Closed S := by
    intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨BinaryFive.base i j, Finset.mem_univ _, hf i j⟩
  have ha : a ∈ S := Finset.mem_map.mpr ⟨0, Finset.mem_univ _, hf0⟩
  have hb : b ∈ S := Finset.mem_map.mpr ⟨1, Finset.mem_univ _, hf1⟩
  refine ⟨⟨S,hcard,hclosed⟩, ⟨ha,hb⟩, ?_⟩
  intro T hT
  apply Subtype.ext
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact generated f hf T.val T.property.2 (hf0 ▸ hT.1) (hf1 ▸ hT.2) i
  · simp only [hcard, T.property.1, le_refl]

/-- Two blocks sharing two distinct points are the same block. -/
theorem unique {S T : Block Q} {a b : Q} (hab : a ≠ b)
    (haS : a ∈ S.val) (hbS : b ∈ S.val) (haT : a ∈ T.val) (hbT : b ∈ T.val) : S = T :=
  (cover h hc hi a b hab).unique ⟨haS,hbS⟩ ⟨haT,hbT⟩

abbrev BlockAt (a : Q) := {S : Block Q // a ∈ S.val}

/-- The other points are partitioned into four-point sets by blocks through a. -/
noncomputable def pointEquiv (a : Q) :
    (Σ S : BlockAt a, ↥(S.val.val.erase a)) ≃ {x : Q // x ≠ a} :=
  Equiv.ofBijective
    (fun p => ⟨p.2.val, (Finset.mem_erase.mp p.2.property).1⟩) (by
      constructor
      · rintro ⟨S,x⟩ ⟨T,y⟩ he
        have hxy : x.val = y.val := congrArg Subtype.val he
        have hST : S = T := by
          apply Subtype.ext
          exact unique h hc hi (Finset.mem_erase.mp x.property).1
            (Finset.mem_erase.mp x.property).2 S.property
            (hxy ▸ (Finset.mem_erase.mp y.property).2) T.property
        subst T
        have heq : x = y := Subtype.ext hxy
        subst y
        rfl
      · intro x
        obtain ⟨S,hS,_⟩ := cover h hc hi a x.val x.property.symm
        exact ⟨⟨⟨S,hS.1⟩,⟨x.val,Finset.mem_erase.mpr ⟨x.property,hS.2⟩⟩⟩, rfl⟩)

theorem point_count (a : Q) : 4 * Nat.card (BlockAt a) = Nat.card Q - 1 := by
  letI := Fintype.ofFinite Q
  have hh := Fintype.card_congr (pointEquiv h hc hi a)
  have hb (S : BlockAt a) : Fintype.card ↥(S.val.val.erase a) = 4 := by
    simp only [Fintype.card_coe, Finset.card_erase_of_mem S.property, S.val.property.1]
  simpa only [Fintype.card_sigma, hb, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_subtype_compl, Fintype.card_unique, Nat.card_eq_fintype_card,
    Nat.mul_comm] using hh

/-- Ordered distinct pairs are partitioned by their unique five-point block. -/
noncomputable def pairEquiv :
    (Σ S : Block Q, Σ a : ↥S.val, ↥(S.val.erase a.val)) ≃
      {p : Q × Q // p.1 ≠ p.2} :=
  Equiv.ofBijective (fun p => ⟨(p.2.1.val,p.2.2.val),
    (Finset.mem_erase.mp p.2.2.property).1.symm⟩) (by
      constructor
      · rintro ⟨S,a,b⟩ ⟨T,c,d⟩ he
        have hac : a.val = c.val := congrArg (fun z => z.val.1) he
        have hbd : b.val = d.val := congrArg (fun z => z.val.2) he
        have hST : S = T := unique h hc hi
          (Finset.mem_erase.mp b.property).1.symm a.property
          (Finset.mem_erase.mp b.property).2 (hac ▸ c.property)
          (hbd ▸ (Finset.mem_erase.mp d.property).2)
        subst T
        have hac' : a = c := Subtype.ext hac
        subst c
        have hbd' : b = d := Subtype.ext hbd
        subst d
        rfl
      · rintro ⟨⟨a,b⟩,hab⟩
        obtain ⟨S,hS,_⟩ := cover h hc hi a b hab
        exact ⟨⟨S,⟨a,hS.1⟩,⟨b,Finset.mem_erase.mpr ⟨hab.symm,hS.2⟩⟩⟩,rfl⟩)

theorem pair_count : 20 * Nat.card (Block Q) = Nat.card Q * (Nat.card Q - 1) := by
  letI := Fintype.ofFinite Q
  have hh := Fintype.card_congr (pairEquiv h hc hi)
  have hb (S : Block Q) (a : ↥S.val) : Fintype.card ↥(S.val.erase a.val) = 4 := by
    simp only [Fintype.card_coe, Finset.card_erase_of_mem a.property, S.property.1]
  have hdiag : Fintype.card {p : Q × Q // p.1 = p.2} = Fintype.card Q := by
    apply Fintype.card_congr
    exact {
      toFun := fun p => p.val.1
      invFun := fun x => ⟨(x,x),rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl p.property)
      right_inv := fun _ => rfl }
  simp only [Fintype.card_sigma, hb, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_prod, hdiag] at hh
  simp only [show ∀ S : Block Q, S.val.card = 5 from fun S => S.property.1] at hh
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  simp only [Nat.card_eq_fintype_card, Nat.mul_sub_left_distrib, Nat.mul_one]
  nlinarith

/-- The usual design divisibility restriction is necessary, including for
nonmedial commutative idempotent E667 algebras. -/
theorem card_mod_twenty [Nonempty Q] : Nat.card Q % 20 = 1 ∨ Nat.card Q % 20 = 5 := by
  let a : Q := Classical.choice inferInstance
  have h4 := point_count h hc hi a
  have h20 := pair_count h hc hi
  have hp : 0 < Nat.card Q := Nat.card_pos
  have h5 : 5 ∣ Nat.card Q * (Nat.card Q - 1) := by
    rw [← h20]
    exact dvd_mul_of_dvd_left (by decide : 5 ∣ 20) _
  have hh := (show Nat.Prime 5 by decide).dvd_mul.mp h5
  rcases hh with hh | hh
  · have := Nat.mod_eq_zero_of_dvd hh
    omega
  · have := Nat.mod_eq_zero_of_dvd hh
    omega

/-- Every intrinsic block has mean-algebra coordinates, not just the right size. -/
theorem block_coordinates (S : Block Q) :
    ∃ e : ↥S.val ≃ ZMod 5, ∀ i j,
      ((e.symm (BinaryFive.base i j)).val) = (e.symm i).val ◇ (e.symm j).val := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
    (show 1 < S.val.card by rw [S.property.1]; omega)
  obtain ⟨f,hf0,hf1,hf⟩ := CommutativeBlocks.five_embedding h hc hi a b hab
  have hmem (i) : f i ∈ S.val := generated f hf S.val S.property.2 (hf0 ▸ ha) (hf1 ▸ hb) i
  let g : ZMod 5 → ↥S.val := fun i => ⟨f i,hmem i⟩
  have hg : Function.Injective g := fun i j he => f.injective (congrArg Subtype.val he)
  have hcard : Fintype.card (ZMod 5) = Fintype.card ↥S.val := by
    simp only [Fintype.card_coe, S.property.1]
    rfl
  let E := Equiv.ofBijective g ⟨hg,(Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hcard⟩ |>.2⟩
  exact ⟨E.symm, hf⟩

omit hi in
/-- In any globally commutative E667 magma, the nonempty idempotent set
itself satisfies the five-design congruence. -/
theorem idempotents_mod_twenty [Nonempty {x : Q // x ◇ x = x}] :
    Nat.card {x : Q // x ◇ x = x} % 20 = 1 ∨
    Nat.card {x : Q // x ◇ x = x} % 20 = 5 := by
  letI : Magma {x : Q // x ◇ x = x} := ⟨fun x y => ⟨x.val ◇ y.val, by
    rw [square_hom_of_commutative h hc, x.property, y.property]⟩⟩
  apply card_mod_twenty
  · intro x y; exact Subtype.ext (h x.val y.val)
  · intro x y; exact Subtype.ext (hc x.val y.val)
  · intro x; exact Subtype.ext x.property

spectrum_assert block_coordinates complete
spectrum_assert idempotents_mod_twenty complete
spectrum_assert card_mod_twenty complete
spectrum_assert pair_count complete
spectrum_assert cover complete
spectrum_assert point_count complete
end Spectrum.E667.CommutativeDesign

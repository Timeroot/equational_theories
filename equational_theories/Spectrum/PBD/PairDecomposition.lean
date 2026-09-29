import equational_theories.Spectrum.PBD.Existence

/-!
Pair decompositions, the common language for PBDs and group-divisible designs.
The block-size set may be infinite: Wilson's proof applies these constructions
to the set of replication numbers as well as to a finite set of generators.
-/
namespace Spectrum.PBD
open Classical

/-- A decomposition of the distinct pairs satisfying `R` into complete blocks.
For a PBD take `R := fun _ _ => True`; for a GDD take
`R := fun x y => group x ≠ group y`. -/
structure PairDecomposition (K : Set ℕ) (X : Type*) (R : X → X → Prop) where
  blocks : Finset (Set X)
  sizes : ∀ b ∈ blocks, Nat.card b ∈ K
  sound : ∀ b ∈ blocks, ∀ x ∈ b, ∀ y ∈ b, x ≠ y → R x y
  cover : ∀ x y, x ≠ y → R x y → ∃! b : blocks, x ∈ b.val ∧ y ∈ b.val

namespace PairDecomposition
variable {K L : Set ℕ} {X Y I : Type*} {R : X → X → Prop}

/-- Finite indexed block families may be used without proving that their
empty or singleton blocks have distinct indices. -/
noncomputable def ofIndexed [Finite I] (B : I → Set X)
    (sizes : ∀ i, Nat.card (B i) ∈ K)
    (sound : ∀ i x, x ∈ B i → ∀ y, y ∈ B i → x ≠ y → R x y)
    (cover : ∀ x y, x ≠ y → R x y → ∃! i, x ∈ B i ∧ y ∈ B i) :
    PairDecomposition K X R := by
  letI := Fintype.ofFinite I
  refine ⟨Finset.univ.image B, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact sizes i
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact sound i
  · intro x y hxy hR
    obtain ⟨i, hi, hu⟩ := cover x y hxy hR
    refine ⟨⟨B i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩, hi, ?_⟩
    rintro ⟨b, hb⟩ h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact Subtype.ext (congrArg B (hu j h))

def mono (D : PairDecomposition K X R) (h : K ⊆ L) :
    PairDecomposition L X R :=
  { D with sizes := fun b hb => h (D.sizes b hb) }

def congr (D : PairDecomposition K X R) {S : X → X → Prop}
    (h : ∀ x y, x ≠ y → (R x y ↔ S x y)) : PairDecomposition K X S :=
  { D with
    sound := fun b hb x hx y hy hxy => (h x y hxy).mp (D.sound b hb x hx y hy hxy)
    cover := fun x y hxy hS => D.cover x y hxy ((h x y hxy).mpr hS) }

noncomputable def transport (D : PairDecomposition K X R) (e : X ≃ Y) :
    PairDecomposition K Y (fun x y => R (e.symm x) (e.symm y)) := by
  apply ofIndexed (fun b : D.blocks => e '' b.val)
  · intro b
    rw [← Nat.card_congr (Equiv.Set.image e b.val e.injective)]
    exact D.sizes b.val b.property
  · intro b x hx y hy hxy
    have hx' : e.symm x ∈ b.val := by simpa using hx
    have hy' : e.symm y ∈ b.val := by simpa using hy
    exact D.sound _ b.property _ hx' _ hy' (fun h => hxy (e.symm.injective h))
  · intro x y hxy hR
    obtain ⟨b, hb, hu⟩ := D.cover (e.symm x) (e.symm y)
      (fun h => hxy (e.symm.injective h)) hR
    refine ⟨b, ?_, ?_⟩
    · simpa using hb
    · intro c hc
      exact hu c (by simpa using hc)

/-- A complete design on a finite carrier. -/
abbrev Complete (K : Set ℕ) (X : Type*) := PairDecomposition K X (fun _ _ => True)

noncomputable def singleBlock (h : Nat.card X ∈ K) : Complete K X :=
  ofIndexed (I := Unit) (fun _ => Set.univ)
    (fun _ => by simpa using h)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => ⟨(), ⟨trivial,trivial⟩, fun _ _ => rfl⟩)

/-- Refine each block independently, preserving the pairs being decomposed. -/
noncomputable def refine (D : PairDecomposition K X R)
    (E : ∀ b : D.blocks, Complete L b.val) : PairDecomposition L X R := by
  let B (i : Σ b : D.blocks, (E b).blocks) : Set X := Subtype.val '' i.2.val
  apply ofIndexed B
  · intro i
    have e : i.2.val ≃ B i := Equiv.Set.imageOfInjOn Subtype.val i.2.val
      (Subtype.val_injective.injOn)
    rw [← Nat.card_congr e]
    exact (E i.1).sizes _ i.2.property
  · rintro ⟨b,c⟩ x ⟨x',hx',rfl⟩ y ⟨y',hy',rfl⟩ hxy
    exact D.sound _ b.property _ x'.property _ y'.property hxy
  · intro x y hxy hR
    obtain ⟨b, ⟨hx,hy⟩, hu⟩ := D.cover x y hxy hR
    obtain ⟨c, hc, hv⟩ := (E b).cover ⟨x,hx⟩ ⟨y,hy⟩
      (fun h => hxy (congrArg Subtype.val h)) trivial
    refine ⟨⟨b,c⟩, ⟨⟨⟨x,hx⟩,hc.1,rfl⟩,⟨⟨y,hy⟩,hc.2,rfl⟩⟩, ?_⟩
    rintro ⟨b',c'⟩ ⟨⟨x',hx',heqx⟩,⟨y',hy',heqy⟩⟩
    have hb : b' = b := hu b' ⟨heqx ▸ x'.property, heqy ▸ y'.property⟩
    subst b'
    have hx'val : x' = ⟨x,hx⟩ := Subtype.ext heqx
    have hy'val : y' = ⟨y,hy⟩ := Subtype.ext heqy
    have hc' : c' = c := hv c' ⟨hx'val ▸ hx',hy'val ▸ hy'⟩
    subst c'
    rfl

/-- Assemble complete designs on an indexed pair cover. Keeping the original
indices makes it possible to track individual blocks through constructions. -/
noncomputable def assemble [Finite I] (B : I → Set X)
    (cover : ∀ x y, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)
    (E : ∀ i, Complete K (B i)) : Complete K X := by
  let C (i : Σ i, (E i).blocks) : Set X := Subtype.val '' i.2.val
  apply ofIndexed C
  · intro i
    rw [← Nat.card_congr (Equiv.Set.image Subtype.val i.2.val Subtype.val_injective)]
    exact (E i.1).sizes _ i.2.property
  · exact fun _ _ _ _ _ _ => trivial
  · intro x y hxy _
    obtain ⟨i,⟨hx,hy⟩,hu⟩ := cover x y hxy
    obtain ⟨c,hc,hv⟩ := (E i).cover ⟨x,hx⟩ ⟨y,hy⟩
      (fun h => hxy (congrArg Subtype.val h)) trivial
    refine ⟨⟨i,c⟩,⟨⟨⟨x,hx⟩,hc.1,rfl⟩,⟨⟨y,hy⟩,hc.2,rfl⟩⟩,?_⟩
    rintro ⟨j,d⟩ ⟨⟨x',hx',heqx⟩,⟨y',hy',heqy⟩⟩
    have hij : j = i := hu j ⟨heqx ▸ x'.property,heqy ▸ y'.property⟩
    subst j
    have hxx : x' = ⟨x,hx⟩ := Subtype.ext heqx
    have hyy : y' = ⟨y,hy⟩ := Subtype.ext heqy
    have hd : d = c := hv d ⟨hxx ▸ hx',hyy ▸ hy'⟩
    subst d
    rfl

theorem assemble_mem [Finite I] (B : I → Set X)
    (cover : ∀ x y, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)
    (E : ∀ i, Complete K (B i)) (i : I) (c : (E i).blocks) :
    Subtype.val '' c.val ∈ (assemble B cover E).blocks := by
  letI := Fintype.ofFinite (Σ i, (E i).blocks)
  exact Finset.mem_image.mpr ⟨⟨i,c⟩,Finset.mem_univ _,rfl⟩

theorem singleBlock_mem (h : Nat.card X ∈ K) :
    Set.univ ∈ (singleBlock h).blocks := by
  letI := Fintype.ofFinite Unit
  exact Finset.mem_image.mpr ⟨(),Finset.mem_univ _,rfl⟩

theorem transport_mem (D : PairDecomposition K X R) (e : X ≃ Y) (b : D.blocks) :
    e '' b.val ∈ (D.transport e).blocks := by
  letI := Fintype.ofFinite D.blocks
  exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩

/-- A designated block of a specified size is available for later deletion. -/
def ContainsBlock (D : PairDecomposition K X R) (s : ℕ) : Prop :=
  ∃ b ∈ D.blocks, Nat.card b = s

theorem ContainsBlock.transport {D : PairDecomposition K X R} {s : ℕ}
    (h : D.ContainsBlock s) (e : X ≃ Y) : (D.transport e).ContainsBlock s := by
  obtain ⟨b,hb,hs⟩ := h
  refine ⟨e '' b,D.transport_mem e ⟨b,hb⟩,?_⟩
  rw [← Nat.card_congr (Equiv.Set.image e b e.injective)]
  exact hs

theorem assemble_contains [Finite I] (B : I → Set X)
    (cover : ∀ x y, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)
    (E : ∀ i, Complete K (B i)) (i : I) {s : ℕ}
    (h : (E i).ContainsBlock s) : (assemble B cover E).ContainsBlock s := by
  obtain ⟨c,hc,hs⟩ := h
  refine ⟨Subtype.val '' c,assemble_mem B cover E i ⟨c,hc⟩,?_⟩
  rw [← Nat.card_congr (Equiv.Set.image Subtype.val c Subtype.val_injective)]
  exact hs

theorem singleBlock_contains (h : Nat.card X ∈ K) :
    (singleBlock h).ContainsBlock (Nat.card X) :=
  ⟨Set.univ,singleBlock_mem h,by simp⟩

noncomputable def toPairwiseBalanced {n : ℕ} {K : Finset ℕ}
    (D : Complete (K : Set ℕ) (Fin n)) : PairwiseBalanced K n := by
  let B (b : D.blocks) : Finset (Fin n) := b.val.toFinset
  refine ⟨Finset.univ.image B, ?_, ?_⟩
  · intro b hb
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
    simpa [B, Nat.card_eq_fintype_card] using D.sizes _ c.property
  · intro x y hxy
    obtain ⟨b,hb,hu⟩ := D.cover x y hxy trivial
    refine ⟨⟨B b, Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩,
      ⟨by simpa [B] using hb.1,by simpa [B] using hb.2⟩, ?_⟩
    rintro ⟨c,hc⟩ h
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hc
    exact Subtype.ext (congrArg B (hu d (by simpa [B] using h)))

end PairDecomposition
end Spectrum.PBD

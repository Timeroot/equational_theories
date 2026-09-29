import equational_theories.Spectrum.PBD.Adjoin

/-! PBD closure, including infinite sets of permitted block sizes. -/
namespace Spectrum.PBD
open Classical PairDecomposition

/-- The set of orders constructible with blocks from `K`. -/
def designClosure (K : Set ℕ) : Set ℕ :=
  {n | Nonempty (Complete K (Fin n))}

/-- Zero is included, using the empty design. -/
def DesignClosed (K : Set ℕ) : Prop := designClosure K ⊆ K

noncomputable def PairDecomposition.ofCard {K : Set ℕ} {X Y : Type*}
    [Finite X] [Finite Y] (D : Complete K X) (h : Nat.card Y = Nat.card X) :
    Complete K Y :=
  D.transport (Finite.card_eq.mp h.symm).some

theorem mem_designClosure {K : Set ℕ} {X : Type*} [Finite X] (D : Complete K X) :
    Nat.card X ∈ designClosure K :=
  ⟨D.ofCard (by simp)⟩

noncomputable def designOfMem {K : Set ℕ} {X : Type*} [Finite X]
    (h : Nat.card X ∈ designClosure K) : Complete K X :=
  (Classical.choice h).ofCard (by simp)

theorem subset_designClosure (K : Set ℕ) : K ⊆ designClosure K := by
  intro n hn
  exact ⟨singleBlock (by simpa using hn)⟩

theorem designClosure_mono {K L : Set ℕ} (h : K ⊆ L) :
    designClosure K ⊆ designClosure L := by
  rintro n ⟨D⟩
  exact ⟨D.mono h⟩

theorem designClosure_closed (K : Set ℕ) : DesignClosed (designClosure K) := by
  rintro n ⟨D⟩
  exact ⟨D.refine (fun b => designOfMem (D.sizes _ b.property))⟩

theorem DesignClosed.apply {K : Set ℕ} (h : DesignClosed K)
    {X : Type*} [Finite X] (D : Complete K X) : Nat.card X ∈ K :=
  h (mem_designClosure D)

noncomputable def PairDecomposition.empty {K : Set ℕ} {X : Type*} [Subsingleton X] :
    Complete K X where
  blocks := ∅
  sizes := by simp
  sound := by simp
  cover := fun x y h _ => (h (Subsingleton.elim x y)).elim

theorem zero_mem_designClosure (K : Set ℕ) : 0 ∈ designClosure K :=
  ⟨PairDecomposition.empty⟩

theorem one_mem_designClosure (K : Set ℕ) : 1 ∈ designClosure K :=
  ⟨PairDecomposition.empty⟩

theorem DesignClosed.zero_mem {K : Set ℕ} (h : DesignClosed K) : 0 ∈ K :=
  h (zero_mem_designClosure K)

theorem DesignClosed.one_mem {K : Set ℕ} (h : DesignClosed K) : 1 ∈ K :=
  h (one_mem_designClosure K)

theorem designClosure_finset {K : Finset ℕ} {n : ℕ} :
    n ∈ designClosure (K : Set ℕ) ↔ HasPBD K n := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.toPairwiseBalanced⟩
  · rintro ⟨D⟩
    refine ⟨ofIndexed (fun b : D.blocks => (b.val : Set (Fin n))) ?_
      (fun _ _ _ _ _ _ => trivial) (fun x y h _ => D.cover x y h)⟩
    intro b
    simpa using D.sizes b.val b.property

end Spectrum.PBD

import equational_theories.Spectrum.PBD.PairDecomposition

/-! Wilson's fundamental construction: replace every point by a fibre and
every block by a group-divisible design on those fibres. -/
namespace Spectrum.PBD.PairDecomposition
open Classical
variable {K L : Set ℕ} {X : Type*} {R : X → X → Prop}

def fibreEmbedding (W : X → Type*) (b : Set X) :
    (Σ x : b, W x.val) ↪ (Σ x, W x) :=
  Function.Embedding.sigmaMap (Function.Embedding.subtype b)
    (fun _ => Function.Embedding.refl _)

/-- Wilson's weighted fundamental construction, before reassembling the
outer groups. An ingredient's groups are indexed by the points of its block. -/
noncomputable def inflate (D : PairDecomposition K X R) (W : X → Type*)
    (E : ∀ b : D.blocks,
      PairDecomposition L (Σ x : b.val, W x.val) (fun x y => x.1 ≠ y.1)) :
    PairDecomposition L (Σ x, W x) (fun x y => x.1 ≠ y.1 ∧ R x.1 y.1) := by
  let B (i : Σ b : D.blocks, (E b).blocks) : Set (Σ x, W x) :=
    fibreEmbedding W i.1.val '' i.2.val
  apply ofIndexed B
  · intro i
    rw [← Nat.card_congr (Equiv.Set.image (fibreEmbedding W i.1.val) i.2.val
      (fibreEmbedding W i.1.val).injective)]
    exact (E i.1).sizes _ i.2.property
  · rintro ⟨b,c⟩ x ⟨x',hx',rfl⟩ y ⟨y',hy',rfl⟩ hxy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg (fibreEmbedding W b.val) h)
    have hp := (E b).sound _ c.property _ hx' _ hy' hxy'
    have hv : x'.1.val ≠ y'.1.val := fun h => hp (Subtype.ext h)
    exact ⟨hv, D.sound _ b.property _ x'.1.property _ y'.1.property hv⟩
  · rintro ⟨x,u⟩ ⟨y,v⟩ _ ⟨hxy,hR⟩
    obtain ⟨b,⟨hx,hy⟩,hu⟩ := D.cover x y hxy hR
    let x' : Σ z : b.val, W z.val := ⟨⟨x,hx⟩,u⟩
    let y' : Σ z : b.val, W z.val := ⟨⟨y,hy⟩,v⟩
    have hf : x'.1 ≠ y'.1 := fun h => hxy (congrArg Subtype.val h)
    obtain ⟨c,hc,hv⟩ := (E b).cover x' y' (fun h => hf (congrArg Sigma.fst h)) hf
    refine ⟨⟨b,c⟩, ⟨⟨x',hc.1,rfl⟩,⟨y',hc.2,rfl⟩⟩, ?_⟩
    rintro ⟨b',c'⟩ ⟨⟨a,ha,heqa⟩,⟨d,hd,heqd⟩⟩
    have hax : a.1.val = x := congrArg Sigma.fst heqa
    have hdy : d.1.val = y := congrArg Sigma.fst heqd
    have hb : b' = b := hu b' ⟨hax ▸ a.1.property,hdy ▸ d.1.property⟩
    subst b'
    have ha' : a = x' := (fibreEmbedding W b.val).injective heqa
    have hd' : d = y' := (fibreEmbedding W b.val).injective heqd
    have hc' : c' = c := hv c' ⟨ha' ▸ ha,hd' ▸ hd⟩
    subst c'
    rfl

/-- A group-divisible design with explicitly indexed groups. -/
abbrev GroupDivisible (K : Set ℕ) {I : Type*} (A : I → Type*) :=
  PairDecomposition K (Σ i, A i) (fun x y => x.1 ≠ y.1)

/-- The fundamental construction with its resulting groups made explicit. -/
noncomputable def fundamental {I : Type*} {A : I → Type*}
    (D : GroupDivisible K A) (W : (Σ i, A i) → Type*)
    (E : ∀ b : D.blocks, GroupDivisible L (fun x : b.val => W x.val)) :
    GroupDivisible L (fun i => Σ x : A i, W ⟨i,x⟩) := by
  let e : (Σ x : (Σ i, A i), W x) ≃ (Σ i, Σ x : A i, W ⟨i,x⟩) :=
    Equiv.sigmaAssoc (fun i x => W ⟨i,x⟩)
  apply ((D.inflate W E).transport e).congr
  rintro ⟨i,x,u⟩ ⟨j,y,v⟩ _
  change ((⟨i,x⟩ : Σ i, A i) ≠ ⟨j,y⟩ ∧ i ≠ j) ↔ i ≠ j
  exact ⟨And.right, fun h => ⟨fun he => h (congrArg Sigma.fst he),h⟩⟩

end Spectrum.PBD.PairDecomposition

import equational_theories.Spectrum.PBD.HoleGroups
import equational_theories.Spectrum.PBD.Transversal

/-! A coordinate form of the fundamental construction for transversal recipes. -/
namespace Spectrum.PBD.Transversal
open Classical PairDecomposition
variable {K : Set ℕ} {I Q : Type*} (T : Transversal I Q) (W : I → Q → Type*)

def weightedEmbedding (p : Q × Q) :
    (Σ i, W i (T.line p i)) ↪ (Σ i, Σ x, W i x) :=
  Function.Embedding.sigmaMap (Function.Embedding.refl I)
    (fun i => Function.Embedding.sigmaMk (T.line p i))

/-- Replace each point of a TD by a fibre and fill each original line with
an ingredient GDD whose group sizes are those fibres. -/
noncomputable def weighted [Finite Q]
    (E : ∀ p : Q × Q, GroupDivisible K (fun i => W i (T.line p i))) :
    GroupDivisible K (fun i => Σ x, W i x) := by
  let B (i : Σ p, (E p).blocks) : Set (Σ i, Σ x, W i x) :=
    weightedEmbedding T W i.1 '' i.2.val
  apply ofIndexed B
  · intro i
    rw [← Nat.card_congr (Equiv.Set.image (weightedEmbedding T W i.1) i.2.val
      (weightedEmbedding T W i.1).injective)]
    exact (E i.1).sizes _ i.2.property
  · rintro ⟨p,b⟩ x ⟨x',hx',rfl⟩ y ⟨y',hy',rfl⟩ hxy
    exact (E p).sound _ b.property _ hx' _ hy'
      (fun h => hxy (congrArg (weightedEmbedding T W p) h))
  · rintro ⟨i,x,u⟩ ⟨j,y,v⟩ _ hij
    obtain ⟨p,hp⟩ := (T.pair i j hij).surjective (x,y)
    obtain ⟨hx,hy⟩ := Prod.mk.inj hp
    subst x
    subst y
    let u' : Σ i, W i (T.line p i) := ⟨i,u⟩
    let v' : Σ i, W i (T.line p i) := ⟨j,v⟩
    obtain ⟨b,hb,hu⟩ := (E p).cover u' v' (fun h => hij (congrArg (fun z : Σ i, W i (T.line p i) => z.1) h)) hij
    refine ⟨⟨p,b⟩,⟨⟨u',hb.1,rfl⟩,⟨v',hb.2,rfl⟩⟩,?_⟩
    rintro ⟨q,c⟩ ⟨⟨s,hs,heqs⟩,⟨t,ht,heqt⟩⟩
    have hsi : s.1 = i := congrArg Sigma.fst heqs
    have htj : t.1 = j := congrArg Sigma.fst heqt
    have hq1 : T.line q s.1 = T.line p i := congrArg (fun z => z.2.1) heqs
    have hq2 : T.line q t.1 = T.line p j := congrArg (fun z => z.2.1) heqt
    rw [hsi] at hq1
    rw [htj] at hq2
    have hqp : q = p := (T.pair i j hij).injective (Prod.ext hq1 hq2)
    subst q
    have hsu : s = u' := (weightedEmbedding T W p).injective heqs
    have htv : t = v' := (weightedEmbedding T W p).injective heqt
    have hcb : c = b := hu c ⟨hsu ▸ hs,htv ▸ ht⟩
    subst c
    rfl

end Spectrum.PBD.Transversal

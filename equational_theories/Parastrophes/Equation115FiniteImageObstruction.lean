import equational_theories.Parastrophes.FiniteAbelianSeparation
import equational_theories.Parastrophes.Equation115RightImage
import equational_theories.Parastrophes.Equation115SquareTranslations
import equational_theories.Parastrophes.Attributes

/-!
# The finite right image of E115 is not equational

Boolean NOT-left-AND-right is not a right quasigroup, but satisfies every
identity true in all finite E115 right images. We simulate its term values
with the completed integer turn, then preserve each finite computation by
finite additive quotients and triangle trades. Thus no single equation of
any length characterizes the finite image.
-/
namespace Parastrophes.Eq115BooleanTurn
noncomputable section
open Law FreeMagma

private def tripleHeight : W →+ W :=
  { toFun := fun x => (3*x.1,x.2), map_zero' := rfl,
    map_add' := fun x y => by apply Prod.ext <;> simp; ring }

private theorem tripleHeight_injective : Function.Injective tripleHeight := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext
  · change 3*x.1=3*y.1 at h1
    omega
  · exact h2

private theorem shifted_nonzero (x : W) : tripleHeight x+s ≠ 0 := by
  intro h
  have hh := congrArg height h
  change 3*x.1+1=0 at hh
  omega

private theorem tripleHeight_s : tripleHeight s=s+s+s := by rfl

/-- Preserve finite computations in common witnesses: E115 right images
whose opposite divisions are also E873 left images. -/
theorem finite_fragment_common (c : Completed) (P : Finset (W × W)) (S : Finset W) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : W → G),
      InImage Law115 .right D ∧ InImage Law873.dual .right D ∧ Set.InjOn e (↑S : Set W) ∧
      ∀ p ∈ P, D.op (e p.1) (e p.2) = e (p.2-c.turn (p.1-p.2)) := by
  classical
  let F := insert 0 (P.image fun p => p.1-p.2)
  let C := F ∪ F.image c.turn ∪ F.image (fun x => c.turn (c.turn x))
  have hF (x) (hx : x ∈ F) : x ∈ C := Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have closed (x) (hx : x ∈ C) : c.turn x ∈ C := by
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      rw [c.cube]
      exact hF y hy
  let B := {x // x ∈ C}
  let p : B → B := fun x => ⟨c.turn (c.turn x.val),closed _ (closed _ x.property)⟩
  have pc (x) : p (p (p x))=x := by
    apply Subtype.ext
    change c.turn (c.turn (c.turn (c.turn (c.turn (c.turn x.val)))))=x.val
    rw [c.cube,c.cube]
  let T := insert 0 (C.image (fun x => tripleHeight x+s) ∪ S.image tripleHeight)
  obtain ⟨V,hV,hfin,f,hf⟩ := finite_separation T
  letI := hV
  letI := hfin
  let H : W →+ V := f.comp tripleHeight
  let v : V := f s
  let points : B → V := fun x => f (tripleHeight x.val+s)
  have memT (x : B) : tripleHeight x.val+s ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩))
  have pinj : Function.Injective points := by
    intro x y h
    apply Subtype.ext
    apply tripleHeight_injective
    exact add_right_cancel (hf (memT x) (memT y) h)
  have pnz (x) : points x ≠ 0 := by
    intro h
    apply shifted_nonzero x.val
    exact hf (memT x) (Finset.mem_insert_self ..) (h.trans f.map_zero.symm)
  have psum (x) : points x + points (p x) + points (p (p x))=0 := by
    have hv : (p (p x)).val=c.turn x.val := by
      change c.turn (c.turn (c.turn (c.turn x.val)))=c.turn x.val
      rw [c.cube]
    change f (tripleHeight x.val+s) + f (tripleHeight (p x).val+s) +
      f (tripleHeight (p (p x)).val+s)=0
    rw [← map_add,← map_add,hv]
    change f ((tripleHeight x.val+s)+(tripleHeight (c.turn (c.turn x.val))+s)+
      (tripleHeight (c.turn x.val)+s))=0
    have he : (tripleHeight x.val+s)+(tripleHeight (c.turn (c.turn x.val))+s)+
        (tripleHeight (c.turn x.val)+s)=0 := by
      calc
        _ = tripleHeight (x.val+c.turn x.val+c.turn (c.turn x.val))+(s+s+s) := by
          simp only [map_add]; abel
        _ = 0 := by rw [c.sum,map_neg,tripleHeight_s]; abel
    rw [he,map_zero]
  obtain ⟨Q,Qcube,Qsum,Qon⟩ := FiniteTriangleTrades.exists_turn_on_points points p pinj pnz pc psum
  let v₂ : V × V := (v,0)
  let A := fun z : V × V => Q (z+v₂)-v₂
  have Acube (z) : A (A (A z))=z := by
    simp only [A,sub_add_cancel,Qcube,add_sub_cancel_right]
  have Aon (x : B) : A (H x.val,0)=(H (c.turn (c.turn x.val)),0) := by
    have hx : (H x.val,0)+v₂=(points x,0) := by
      apply Prod.ext <;> simp [H,v₂,v,points]
    dsimp only [A]
    rw [hx,Qon]
    apply Prod.ext <;> simp [H,v₂,v,points,p]
  have A2on (x : B) : A (A (H x.val,0))=(H (c.turn x.val),0) := by
    rw [Aon x,Aon (p x)]
    change (H (c.turn (c.turn (c.turn (c.turn x.val)))),0)=_
    rw [c.cube]
  let z : B := ⟨0,hF 0 (Finset.mem_insert_self ..)⟩
  have Azero : A 0=(H s,0) := by
    have he := Aon z
    simpa only [z,map_zero,c.zero,c.second] using he
  have Hs : H s=v+v+v := by simp [H,v,tripleHeight_s]
  have Asum (x) : x+A x+A (A x)= -(H s,0) := by
    have he := Qsum (x+v₂)
    dsimp only [A]
    rw [sub_add_cancel]
    calc
      x+(Q (x+v₂)-v₂)+(Q (Q (x+v₂))-v₂) =
          (x+v₂+Q (x+v₂)+Q (Q (x+v₂)))-(v₂+v₂+v₂) := by abel
      _ = -(H s,0) := by rw [he]; simp [v₂,Hs]
  let D := Eq115SquareTranslations.rightDivision A
  let M := Eq115SquareTranslations.source A
  have hi : InImage Law115 .right D :=
    ⟨M,(@Law115.models_iff _ M).mpr (Eq115SquareTranslations.source_law A (H s,0) Azero Asum),
      Eq115SquareTranslations.isRightDivision A Acube⟩
  have hi873 : InImage Law873.dual .right D := by
    refine ⟨M,?_,Eq115SquareTranslations.isRightDivision A Acube⟩
    apply (satisfies_opposite (opposite M) Law873).mpr
    exact (@Law873.models_iff _ (opposite M)).mpr
      (Eq115SquareTranslations.opposite_source_law873 A (H s,0) Azero Asum Acube)
  refine ⟨V×V,inferInstance,D,fun x => (H x,0),hi,hi873,?_,?_⟩
  · intro x hx y hy he
    apply tripleHeight_injective
    exact hf
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)))
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)))
      (congrArg Prod.fst he)
  · intro xy hxy
    let q : B := ⟨xy.1-xy.2,hF _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨xy,hxy,rfl⟩))⟩
    change (H xy.2,0)-A (A ((H xy.1,0)-(H xy.2,0)))=(H (xy.2-c.turn (xy.1-xy.2)),0)
    have he : (H xy.1,(0:V))-(H xy.2,0)=(H q.val,0) := by simp [q]
    rw [he,A2on q]
    simp [q]

/-- The E115 component of the common finite construction. -/
theorem finite_fragment (c : Completed) (P : Finset (W × W)) (S : Finset W) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : W → G),
      InImage Law115 .right D ∧ Set.InjOn e (↑S : Set W) ∧
      ∀ p ∈ P, D.op (e p.1) (e p.2) = e (p.2-c.turn (p.1-p.2)) := by
  obtain ⟨G,hG,D,e,h115,_,hi,hp⟩ := finite_fragment_common c P S
  exact ⟨G,hG,D,e,h115,hi,hp⟩

@[implicit_reducible] private def simulation (c : Completed) : Magma W := ⟨fun x y => y-c.turn (x-y)⟩
private def inputs (v : ℕ → Bool) (i : ℕ) : W := if v i then 0 else s
private def value (c : Completed) (v : ℕ → Bool) (t : FreeMagma ℕ) :=
  @evalInMagma _ _ (simulation c) (inputs v) t

private theorem value_color (c : Completed) (v : ℕ → Bool) (t : FreeMagma ℕ) :
    Positive (value c v t) ∧ color (value c v t) =
      @evalInMagma _ _ Eq115RightImage.booleanCounterexample v t := by
  induction t with
  | Leaf i =>
    change Positive (inputs v i) ∧ color (inputs v i)=v i
    cases h : v i <;> simp [inputs,h,Positive,color]
  | Fork a b ha hb =>
    have hh := simulate ha.1 hb.1 (c.good (value c v a-value c v b))
    exact ⟨hh.1,hh.2.trans (by rw [ha.2,hb.2]; rfl)⟩

private def trace (c : Completed) (v : ℕ → Bool) : FreeMagma ℕ → Finset (W × W)
  | .Leaf _ => ∅
  | .Fork a b => insert (value c v a,value c v b) (trace c v a ∪ trace c v b)

private theorem transfer_value {G : Type} (D : Magma G) (e : W → G)
    (c : Completed) (v : ℕ → Bool) (P : Finset (W × W))
    (hp : ∀ p ∈ P, D.op (e p.1) (e p.2)=e (p.2-c.turn (p.1-p.2)))
    (t : FreeMagma ℕ) (ht : trace c v t ⊆ P) :
    @evalInMagma _ _ D (fun i => e (inputs v i)) t=e (value c v t) := by
  induction t with
  | Leaf i => rfl
  | Fork a b ha hb =>
    have hta : trace c v a ⊆ P := fun p h => ht
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have htb : trace c v b ⊆ P := fun p h => ht
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    change D.op (@evalInMagma _ _ D _ a) (@evalInMagma _ _ D _ b)=_
    rw [ha hta,hb htb]
    exact hp (value c v a,value c v b) (ht (Finset.mem_insert_self ..))

/-- If finite right images realize every simulation fragment, their entire
equational theory holds in Boolean NOT-left-AND-right. -/
theorem boolean_theory_from_fragments (K : NatMagmaLaw)
    (fragments : ∀ (c : Completed) (P : Finset (W × W)) (S : Finset W),
      ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : W → G),
        InImage K .right D ∧ Set.InjOn e (↑S : Set W) ∧
        ∀ p ∈ P, D.op (e p.1) (e p.2)=e (p.2-c.turn (p.1-p.2)))
    (L : NatMagmaLaw)
    (h : ∀ (G : Type) (_hG : Finite G) (D : Magma G), InImage K .right D →
      @satisfies _ G D L) :
    @satisfies _ Bool Eq115RightImage.booleanCounterexample L := by
  classical
  intro v
  let c : Completed := Classical.choice exists_completed
  let a := value c v L.lhs
  let b := value c v L.rhs
  let P := trace c v L.lhs ∪ trace c v L.rhs
  obtain ⟨G,hG,D,e,hi,hinj,hp⟩ := fragments c P {a,b}
  have he := h G hG D hi (fun i => e (inputs v i))
  have hl := transfer_value D e c v P hp L.lhs (by exact Finset.subset_union_left)
  have hr := transfer_value D e c v P hp L.rhs (by exact Finset.subset_union_right)
  have hab : a=b := hinj (by simp) (by simp) (hl.symm.trans (he.trans hr))
  exact (value_color c v L.lhs).2.symm.trans
    ((congrArg color hab).trans (value_color c v L.rhs).2)

/-- Every identity of finite E115 right images holds in the Boolean magma. -/
theorem boolean_theory (L : NatMagmaLaw)
    (h : ∀ (G : Type) (_hG : Finite G) (D : Magma G), InImage Law115 .right D →
      @satisfies _ G D L) :
    @satisfies _ Bool Eq115RightImage.booleanCounterexample L :=
  boolean_theory_from_fragments Law115 finite_fragment L h

/-- There is no single identity of any length characterizing the finite
right-division image of E115. -/
theorem no_singleEquation : ¬ SingleEquation .fin Law115 .right := by
  rintro ⟨L,hL⟩
  apply Eq115RightImage.booleanCounterexample_not_image
  apply (hL Bool Eq115RightImage.booleanCounterexample (inferInstance : Finite Bool)).mp
  exact boolean_theory L (fun G hG D hi => (hL G D hG).mpr hi)

end
end Parastrophes.Eq115BooleanTurn

namespace Parastrophes.Catalogue

/-- Finite triangle trades simulate every Boolean term counterexample in a
finite E115 right image; the Boolean magma itself has nonbijective columns. -/
@[parastrophe_result] theorem right_noSingleEquation115_fin :
    ¬ SingleEquation .fin Law115 .right := Eq115BooleanTurn.no_singleEquation

end Parastrophes.Catalogue

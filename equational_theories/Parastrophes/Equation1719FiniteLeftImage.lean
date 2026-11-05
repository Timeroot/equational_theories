import equational_theories.Parastrophes.FreeGroupDisjointTrades
import equational_theories.Parastrophes.FreeGroupFiniteSeparation
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-!
# No single identity for E1719's finite left-division image

The noncommutative group trades give the following multiplication on protected
pairs of free-group words, where c is a fresh generator chosen from x=(a,b):

    D((a,b),(u,v)) = (u⁻¹ca, v⁻¹a⁻¹b⁻¹c).

The first coordinate grows without cancellation. Hence no composite term,
with all variables equal to the initial pair (g₀,g₁), returns its input.
For any given term, only finitely many trades are used. A finite permutation
representation preserves the distinctions between their nine-point blocks.
Performing the trades in that finite group gives an actual finite E1719
left-division image, preserving the term calculation and its failure.

The last step exhausts all shapes of a proposed single identity: isolated
variable identities are refuted by these finite images, while identities
with two composite sides cannot exclude the two-element constant magma.
-/
namespace Parastrophes.Eq1719FiniteLeftImage
open Law FreeMagma FreeGroupWordCones FreeGroupTradeBlocks FreeGroupTradeLabels
open FreeGroupDisjointTrades GroupTriangleTrades

noncomputable def initial : Input :=
  ⟨(FreeGroup.of 0,FreeGroup.of 1),generator_cone rfl,generator_cone (by decide)⟩

noncomputable def product (x y : Input) : Input :=
  ⟨(y.val.1⁻¹ * letter x * x.val.1,
      y.val.2⁻¹ * x.val.1⁻¹ * x.val.2⁻¹ * letter x),
    (first_product x.property.1 y.property.1 (label_pos x.val)).1,
    second_product x.property.1 x.property.2 y.property.2 (label_pos x.val)
      (fresh_of_label_le x.val le_rfl).2⟩

@[implicit_reducible] noncomputable def inputMagma : Magma Input := ⟨product⟩

noncomputable def value (t : FreeMagma Nat) : Input :=
  @evalInMagma _ _ inputMagma (fun _ => initial) t

noncomputable def values : FreeMagma Nat → Finset Input := by
  classical
  exact fun t => match t with
    | .Leaf _ => {initial}
    | .Fork a b => insert (value (.Fork a b)) (values a ∪ values b)

theorem value_mem (t : FreeMagma Nat) : value t ∈ values t := by
  classical
  cases t <;> simp [values,value,evalInMagma]

theorem value_fork_ne (a b : FreeMagma Nat) : value (a ⋆ b) ≠ initial := by
  intro he
  have hlen := (first_product (value a).property.1 (value b).property.1
    (label_pos (value a).val)).2
  have hv : (value (a ⋆ b)).val.1.toWord.length = 1 := by
    rw [he]
    simp [initial]
  change ((value b).val.1⁻¹ * FreeGroup.of (label (value a).val) *
    (value a).val.1).toWord.length = 1 at hv
  rw [hlen] at hv
  obtain ⟨⟨i,bi,_,hh⟩,_⟩ := (value a).property.1
  have hn : (value a).val.1.toWord ≠ [] := by intro h; simp [h] at hh
  have hp := List.length_pos_iff.mpr hn
  omega

section GroupModel
variable {K : Type} [Group K] (s : K × K → K × K)

@[implicit_reducible] def source : Magma (K × K) := ⟨fun x y => (s (s x))⁻¹ * y⁻¹⟩
@[implicit_reducible] def division : Magma (K × K) := ⟨fun x y => y⁻¹ * (s (s x))⁻¹⟩

variable (hc : ∀ x, s (s (s x)) = x) (ht : ∀ x, x * s (s x) * s x = 1)

include ht in
theorem square_source (x : K × K) : (source s).op x x = s x := by
  change (s (s x))⁻¹ * x⁻¹ = s x
  calc
    _ = ((s (s x))⁻¹ * x⁻¹) * (x * s (s x) * s x) := by rw [ht]; group
    _ = s x := by group

include hc ht in
theorem source_law : @Equation1719 (K × K) (source s) := by
  intro x y
  rw [square_source s ht,square_source s ht]
  change x = (s (s (s y)))⁻¹ * ((s (s (s x)))⁻¹ * y⁻¹)⁻¹
  rw [hc,hc]
  group

theorem isDivision : IsDivision .left (source s) (division s) := by
  constructor <;> intro x y
  · change (s (s x))⁻¹ * (y⁻¹ * (s (s x))⁻¹)⁻¹ = y
    group
  · change ((s (s x))⁻¹ * y⁻¹)⁻¹ * (s (s x))⁻¹ = y
    group

include hc ht in
theorem inImage : InImage Law1719 .left (division s) :=
  ⟨source s,(@Law1719.models_iff (K × K) (source s)).mpr (source_law s hc ht),isDivision s⟩
end GroupModel

/-- Every finite set of protected words embeds into a finite division image.
Products are preserved whenever their left input belongs to that set. -/
theorem finite_fragment (F : Finset Input) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (f : Input → G),
      InImage Law1719 .left D ∧ Set.InjOn f (↑F : Set Input) ∧
      ∀ x ∈ F, ∀ y, D.op (f x) (f y) = f (product x y) := by
  classical
  let B := F
  let X : B → Word × Word := fun b => b.val.val
  let C : B → Word := fun b => letter b.val
  let E := point X C
  have hE : Function.Injective E := by
    rintro ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ he
    have hh : ((x.val,i),j) = ((y.val,k),l) := points_injective he
    obtain ⟨hp,hj⟩ := Prod.mk.inj hh
    obtain ⟨hx,hi⟩ := Prod.mk.inj hp
    have hxy : x=y := Subtype.ext hx
    subst y
    subst k
    subst l
    rfl
  let W : Finset Word := Finset.univ.biUnion fun z : (B × Fin 3) × Fin 3 =>
    {(E z).1,(E z).2}
  have hm (z : (B × Fin 3) × Fin 3) : (E z).1 ∈ W ∧ (E z).2 ∈ W := by
    constructor <;> apply Finset.mem_biUnion.mpr
    · exact ⟨z,Finset.mem_univ _,by simp⟩
    · exact ⟨z,Finset.mem_univ _,by simp⟩
  have hmX (x : Input) (hx : x ∈ F) : x.val.1 ∈ W ∧ x.val.2 ∈ W := by
    simpa [E,X,point,row,orbit] using hm ((⟨x,hx⟩,0),0)
  obtain ⟨U,hU,f,hf⟩ := FreeGroupFiniteSeparation.injective_on_finset W
  let K := Equiv.Perm U
  let g : Input → K × K := fun x => (f x.val.1,f x.val.2)
  have hMap : Function.Injective
      (point (fun b => (f (X b).1,f (X b).2)) (fun b => f (C b))) := by
    intro z w he
    rw [map_point,map_point] at he
    apply hE
    exact Prod.ext (hf (hm z).1 (hm w).1 (congrArg Prod.fst he))
      (hf (hm z).2 (hm w).2 (congrArg Prod.snd he))
  obtain ⟨s,hc,ht,hs⟩ := exists_turn
    (fun b => (f (X b).1,f (X b).2)) (fun b => f (C b)) hMap
  refine ⟨K × K,inferInstance,division s,g,inImage s hc ht,?_,?_⟩
  · intro x hx y hy he
    apply Subtype.ext
    exact Prod.ext (hf (hmX x hx).1 (hmX y hy).1 (congrArg Prod.fst he))
      (hf (hmX x hx).2 (hmX y hy).2 (congrArg Prod.snd he))
  · intro x hx y
    have hsx := hs (⟨x,hx⟩ : B)
    change s (s (g x)) = ((f x.val.1)⁻¹ * (f (letter x))⁻¹,
      (f (letter x))⁻¹ * f x.val.2 * f x.val.1) at hsx
    change (g y)⁻¹ * (s (s (g x)))⁻¹ = g (product x y)
    rw [hsx]
    apply Prod.ext <;> simp [g,product,map_mul,map_inv,mul_assoc]

/-- A finite term calculation transfers through a map preserving the products
at its left subterms. No uniform bound on the term or the finite group is used. -/
theorem eval_map {G : Type} (D : Magma G) (f : Input → G) (F : Finset Input)
    (hp : ∀ x ∈ F, ∀ y, D.op (f x) (f y) = f (product x y))
    (t : FreeMagma Nat) (ht : values t ⊆ F) :
    @evalInMagma _ _ D (fun _ => f initial) t = f (value t) := by
  classical
  induction t with
  | Leaf i => rfl
  | Fork a b ha hb =>
    have hsa : values a ⊆ F := by
      intro x hx
      apply ht
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    have hsb : values b ⊆ F := by
      intro x hx
      apply ht
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
    change D.op (@evalInMagma _ _ D _ a) (@evalInMagma _ _ D _ b) = _
    rw [ha hsa,hb hsb]
    exact hp (value a) (hsa (value_mem a)) (value b)

/-- Every composite term fails an isolated-variable identity in some finite
left-division image of E1719. -/
theorem refute_fork (a b : FreeMagma Nat) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : G),
      InImage Law1719 .left D ∧ @evalInMagma _ _ D (fun _ => e) (a ⋆ b) ≠ e := by
  classical
  let F := insert initial (values (a ⋆ b))
  obtain ⟨G,hG,D,f,hi,hf,hp⟩ := finite_fragment F
  refine ⟨G,hG,D,f initial,hi,?_⟩
  rw [eval_map D f F hp (a ⋆ b) (Finset.subset_insert _ _)]
  intro he
  apply value_fork_ne a b
  exact hf (Finset.mem_insert_of_mem (value_mem _)) (Finset.mem_insert_self _ _) he

@[implicit_reducible] private def constant : Magma Bool := ⟨fun _ _ => false⟩

private theorem constant_not_image : ¬ InImage Law1719 .left constant := by
  rintro ⟨M,_,hd⟩
  have hh := hd.2 false true
  exact Bool.noConfusion hh

/-- No single identity, of any length or number of variables, characterizes
the finite left-division image. -/
theorem no_singleEquation : ¬ SingleEquation .fin Law1719 .left := by
  rintro ⟨⟨l,r⟩,hc⟩
  cases l with
  | Leaf i =>
    cases r with
    | Leaf j =>
      by_cases hij : i=j
      · subst j
        apply constant_not_image
        exact (hc Bool constant (inferInstance : Finite Bool)).1 (fun _ => rfl)
      · obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork (Lf 0) (Lf 0)
        let q := @evalInMagma _ _ D (fun _ => e) ((Lf 0) ⋆ (Lf 0))
        have he := (hc G D hG).2 hi (fun k => if k=i then e else q)
        change (if i=i then e else q) = (if j=i then e else q) at he
        have hji : j ≠ i := fun h => hij h.symm
        have he' : e=q := by simpa only [ite_true,if_neg hji] using he
        exact hn he'.symm
    | Fork a b =>
      obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork a b
      exact hn ((hc G D hG).2 hi (fun _ => e)).symm
  | Fork a b =>
    cases r with
    | Leaf i =>
      obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork a b
      exact hn ((hc G D hG).2 hi (fun _ => e))
    | Fork c d =>
      apply constant_not_image
      exact (hc Bool constant (inferInstance : Finite Bool)).1 (fun _ => rfl)

end Parastrophes.Eq1719FiniteLeftImage

namespace Parastrophes.Catalogue
/-- Noncommutative triangle trades and finite free-group representations give
finite countermodels to every possible isolated-variable image identity. -/
@[parastrophe_result] theorem left_noSingleEquation1719_fin :
    ¬ SingleEquation .fin Law1719 .left := Eq1719FiniteLeftImage.no_singleEquation
end Parastrophes.Catalogue

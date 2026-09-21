import equational_theories.Definability.FORecoveryCompactness
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Counting involutions

Record the smaller endpoint of each two-cycle and its partner. The endpoint
set has at most half the carrier's size. This injects involutions into a family
of at most 2^n n^(n/2) codes, where division in the exponent is natural division.
-/

namespace InvolutionCounting
variable {A : Type} [Fintype A] [LinearOrder A]
abbrev Inv := {f : A → A // Function.Involutive f}

noncomputable def lowerSet (f : A → A) : Finset A := Finset.univ.filter (fun x => x < f x)

theorem mem_lowerSet (f : A → A) (x : A) : x ∈ lowerSet f ↔ x < f x := by
  classical
  simp [lowerSet]

theorem lowerSet_bound (f : Inv (A := A)) : (lowerSet f.val).card ≤ Fintype.card A / 2 := by
  classical
  let S := lowerSet f.val
  have hd : Disjoint S (S.image f.val) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hyS,hxy⟩ := Finset.mem_image.mp hy
    subst x
    have h1 := (mem_lowerSet f.val _).mp hx
    have h2 := (mem_lowerSet f.val _).mp hyS
    rw [f.property y] at h1
    exact (lt_asymm h1 h2)
  have he := Finset.card_union_of_disjoint hd
  rw [Finset.card_image_of_injective S f.property.injective] at he
  have hb := (S ∪ S.image f.val).card_le_univ
  change S.card ≤ Fintype.card A / 2
  omega

abbrev Code := Σ S : {S : Finset A // S.card ≤ Fintype.card A / 2}, (S.val → A)

noncomputable def encode (f : Inv (A := A)) : Code (A := A) :=
  ⟨⟨lowerSet f.val,lowerSet_bound f⟩,fun x => f.val x.val⟩

def partialOp (p : Code (A := A)) (x : A) : A :=
  if h : x ∈ p.1.val then p.2 ⟨x,h⟩ else x

omit [Fintype A] in
theorem agree_at_moved (f g : A → A) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hl : ∀ x, x < f x → f x = g x) (x : A) (hx : f x ≠ x) : f x = g x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have he := hl (f x) (by rw [hf x]; exact hlt)
    have he' : g (f x) = x := he.symm.trans (hf x)
    calc
      f x = g (g (f x)) := (hg (f x)).symm
      _ = g x := congrArg g he'
  · exact hl x hgt

theorem encode_injective : Function.Injective (encode (A := A)) := by
  classical
  intro f g h
  have hs : lowerSet f.val = lowerSet g.val := congrArg (fun p : Code (A := A) => p.1.val) h
  have hfg (x : A) (hx : x < f.val x) : f.val x = g.val x := by
    have hxf := (mem_lowerSet f.val x).mpr hx
    have hxg : x ∈ lowerSet g.val := hs ▸ hxf
    have hh := congrArg (fun p : Code (A := A) => partialOp p x) h
    simpa only [partialOp,encode,dif_pos hxf,dif_pos hxg] using hh
  have hgf (x : A) (hx : x < g.val x) : g.val x = f.val x := by
    have hxg := (mem_lowerSet g.val x).mpr hx
    have hxf : x ∈ lowerSet f.val := hs.symm ▸ hxg
    exact (hfg x ((mem_lowerSet f.val x).mp hxf)).symm
  apply Subtype.ext
  funext x
  by_cases hf : f.val x = x
  · by_cases hg : g.val x = x
    · exact hf.trans hg.symm
    · exact (agree_at_moved g.val f.val g.property f.property hgf x hg).symm
  · exact agree_at_moved f.val g.val f.property g.property hfg x hf

theorem upper_count [Nonempty A] : Nat.card (Inv (A := A)) ≤
    2 ^ Fintype.card A * Fintype.card A ^ (Fintype.card A / 2) := by
  classical
  calc
    _ ≤ Nat.card (Code (A := A)) := Nat.card_le_card_of_injective encode encode_injective
    _ = ∑ S : {S : Finset A // S.card ≤ Fintype.card A / 2}, Fintype.card A ^ S.val.card := by
      simp only [Nat.card_eq_fintype_card,Code,Fintype.card_sigma,Fintype.card_fun,Fintype.card_coe]
    _ ≤ ∑ _S : {S : Finset A // S.card ≤ Fintype.card A / 2},
        Fintype.card A ^ (Fintype.card A / 2) := by
      apply Finset.sum_le_sum
      intro S _
      exact Nat.pow_le_pow_right (Fintype.card_pos) S.property
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
      apply Nat.mul_le_mul_right
      simpa using Fintype.card_subtype_le (fun S : Finset A => S.card ≤ Fintype.card A / 2)

end InvolutionCounting

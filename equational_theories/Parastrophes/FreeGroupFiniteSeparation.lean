import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.List.Infix

/-! A finite permutation representation separates any two distinct free-group
elements. Extend left multiplication on the finite set of suffixes of a word;
the universal property then supplies the representation. -/
namespace Parastrophes.FreeGroupFiniteSeparation

noncomputable section
open FreeGroup

variable {G : Type} [Group G] [DecidableEq G]

def partialTranslation (S : Finset G) (g : G) :
    {x : S // g * x.val ∈ S} ≃ {x : S // g⁻¹ * x.val ∈ S} where
  toFun x := ⟨⟨g * x.val.val, x.property⟩, by simp⟩
  invFun x := ⟨⟨g⁻¹ * x.val.val, x.property⟩, by simp⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

def translation (S : Finset G) (g : G) : Equiv.Perm S := by
  classical
  exact (partialTranslation S g).extendSubtype

theorem translation_apply (S : Finset G) (g : G) (x : S) (hx : g * x.val ∈ S) :
    (translation S g x).val = g * x.val := by
  classical
  exact congrArg Subtype.val ((partialTranslation S g).extendSubtype_apply_of_mem x hx)

theorem translation_inv_apply (S : Finset G) (g : G) (x : S)
    (hx : g⁻¹ * x.val ∈ S) :
    ((translation S g)⁻¹ x).val = g⁻¹ * x.val := by
  have h := translation_apply S g ⟨g⁻¹ * x.val, hx⟩ (by simp)
  have he : translation S g ⟨g⁻¹ * x.val, hx⟩ = x := Subtype.ext (by simpa using h)
  exact congrArg Subtype.val ((Equiv.symm_apply_eq (translation S g)).mpr he.symm)

variable {A : Type} [DecidableEq A]

theorem suffix_action (S : Finset (FreeGroup A)) (h1 : (1 : FreeGroup A) ∈ S)
    (w : List (A × Bool)) (hw : ∀ t, t <:+ w → FreeGroup.mk t ∈ S) :
    ((FreeGroup.lift (fun a => translation S (FreeGroup.of a)))
      (FreeGroup.mk w) ⟨1, h1⟩).val = FreeGroup.mk w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ht : ∀ t, t <:+ w → FreeGroup.mk t ∈ S :=
      fun t h => hw t (h.trans (List.suffix_cons _ _))
    have hi := ih ht
    have hc := hw (a :: w) ⟨[], by simp⟩
    rcases a with ⟨a, b⟩
    cases b
    · change (((translation S (FreeGroup.of a))⁻¹ *
        (FreeGroup.lift (fun a => translation S (FreeGroup.of a)))
          (FreeGroup.mk w)) ⟨1, h1⟩).val = _
      rw [Equiv.Perm.mul_apply, translation_inv_apply S (FreeGroup.of a) _ (by
        rw [hi]; exact hc), hi]
      rfl
    · change ((translation S (FreeGroup.of a) *
        (FreeGroup.lift (fun a => translation S (FreeGroup.of a)))
          (FreeGroup.mk w)) ⟨1, h1⟩).val = _
      rw [Equiv.Perm.mul_apply, translation_apply S (FreeGroup.of a) _ (by
        rw [hi]; exact hc), hi]
      rfl

theorem separate_one (x : FreeGroup A) (hx : x ≠ 1) :
    ∃ (B : Type) (_ : Fintype B) (f : FreeGroup A →* Equiv.Perm B), f x ≠ 1 := by
  classical
  let w := x.toWord
  let S : Finset (FreeGroup A) := (w.tails.map FreeGroup.mk).toFinset
  have hs (t : List (A × Bool)) (ht : t <:+ w) : FreeGroup.mk t ∈ S := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, (List.mem_tails _ _).mpr ht, rfl⟩)
  have h1 : (1 : FreeGroup A) ∈ S := hs [] List.nil_suffix
  let f := FreeGroup.lift (fun a => translation S (FreeGroup.of a))
  refine ⟨S, inferInstance, f, ?_⟩
  intro he
  have ha := suffix_action S h1 w hs
  rw [FreeGroup.mk_toWord] at ha
  change (f x ⟨1, h1⟩).val = x at ha
  rw [he] at ha
  exact hx ha.symm

theorem separate (x y : FreeGroup A) (hxy : x ≠ y) :
    ∃ (B : Type) (_ : Fintype B) (f : FreeGroup A →* Equiv.Perm B), f x ≠ f y := by
  obtain ⟨B, hB, f, hf⟩ := separate_one (x * y⁻¹)
    (fun h => hxy (_root_.mul_inv_eq_one.mp h))
  refine ⟨B, hB, f, ?_⟩
  intro he
  apply hf
  simp [_root_.map_mul, _root_.map_inv, he]

/-- One finite permutation representation preserves all distinctions in a
specified finite set. Include every suffix of every word, so each selected
word acts correctly at the identity in the partial regular representation.
This is useful for transferring a finite family of group trades at once. -/
theorem injective_on_finset (F : Finset (FreeGroup A)) :
    ∃ (B : Type) (_ : Fintype B) (f : FreeGroup A →* Equiv.Perm B),
      Set.InjOn f (↑F : Set (FreeGroup A)) := by
  classical
  let S : Finset (FreeGroup A) := insert 1 (F.biUnion fun x =>
    (x.toWord.tails.map FreeGroup.mk).toFinset)
  have h1 : (1 : FreeGroup A) ∈ S := Finset.mem_insert_self ..
  have hs (x : FreeGroup A) (hx : x ∈ F) (t) (ht : t <:+ x.toWord) :
      FreeGroup.mk t ∈ S := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,List.mem_toFinset.mpr ?_⟩
    exact List.mem_map.mpr ⟨t,(List.mem_tails _ _).mpr ht,rfl⟩
  let f := FreeGroup.lift (fun a => translation S (FreeGroup.of a))
  have he (x : FreeGroup A) (hx : x ∈ F) : (f x ⟨1,h1⟩).val = x := by
    have h := suffix_action S h1 x.toWord (hs x hx)
    simpa only [FreeGroup.mk_toWord] using h
  refine ⟨S,inferInstance,f,?_⟩
  intro x hx y hy hxy
  exact (he x hx).symm.trans ((congrArg (fun p : Equiv.Perm S =>
    (p ⟨1,h1⟩).val) hxy).trans (he y hy))

end
end Parastrophes.FreeGroupFiniteSeparation

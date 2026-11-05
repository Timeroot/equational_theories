import equational_theories.Parastrophes.Catalogue
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Twisted group cores and E1525

An automorphism `s` of order three gives the operation
`M(x,y) = s(x * y⁻¹ * x)`, satisfying E1525. Its left division is
`D(x,y) = x * (s² y)⁻¹ * x`.
-/
namespace Parastrophes.TrialityCore
open Law FreeMagma

section Group
variable {G : Type} [Group G] (s : G →* G) (hs : ∀ x, s (s (s x)) = x)

@[implicit_reducible] def source : Magma G := ⟨fun x y => s (x * y⁻¹ * x)⟩
@[implicit_reducible] def division : Magma G := ⟨fun x y => x * (s (s y))⁻¹ * x⟩

include hs
theorem source_law : @Equation1525 G (source s) := by
  intro x y
  change x = s (s (y * y⁻¹ * y) *
    (s (y * (s (x * x⁻¹ * x))⁻¹ * y))⁻¹ * s (y * y⁻¹ * y))
  simp only [map_mul, map_inv, hs]
  group

theorem isDivision : IsDivision .left (source s) (division s) := by
  constructor
  · intro x y
    change s (x * (x * (s (s y))⁻¹ * x)⁻¹ * x) = y
    simp only [map_mul, map_inv, hs]
    group
  · intro x y
    change x * (s (s (s (x * y⁻¹ * x))))⁻¹ * x = y
    rw [hs]
    group
end Group

abbrev Carrier := FreeGroup (Fin 3)
def rotate (i : Fin 3) : Fin 3 := i + 1
def rotation : Carrier →* Carrier := FreeGroup.map rotate

theorem rotate_three (i : Fin 3) : rotate (rotate (rotate i)) = i := by
  fin_cases i <;> decide

theorem rotation_three (x : Carrier) : rotation (rotation (rotation x)) = x := by
  change FreeGroup.map rotate (FreeGroup.map rotate (FreeGroup.map rotate x)) = x
  rw [FreeGroup.map.comp, FreeGroup.map.comp]
  have he : (rotate ∘ rotate) ∘ rotate = id := funext rotate_three
  rw [he, FreeGroup.map.id]

theorem word_map {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (x : FreeGroup A) :
    (FreeGroup.map f x).toWord = x.toWord.map (fun a => (f a.1, a.2)) := by
  have hr : FreeGroup.IsReduced (x.toWord.map (fun a => (f a.1, a.2))) := by
    apply List.isChain_map_of_isChain _ _ FreeGroup.isReduced_toWord
    intro a b h hab
    exact h (hf hab)
  conv_lhs => rw [← FreeGroup.mk_toWord (x := x)]
  rw [FreeGroup.map.mk, FreeGroup.toWord_mk, hr.reduce_eq]

def bounded (x : Carrier) : Prop :=
  x.toWord.head? = some (0, true) ∧ x.toWord.getLast? = some (0, true)

theorem rotate_injective : Function.Injective rotate := by
  intro a b h
  have := congrArg (fun i => rotate (rotate i)) h
  simpa only [rotate_three] using this

theorem middle_ends {y : Carrier} (hy : bounded y) :
    ((rotation (rotation y))⁻¹).toWord.head? = some (2, false) ∧
    ((rotation (rotation y))⁻¹).toWord.getLast? = some (2, false) := by
  rw [FreeGroup.toWord_inv]
  simp only [rotation, word_map rotate rotate_injective]
  simp [FreeGroup.invRev, List.head?_map, List.getLast?_map,
    List.head?_reverse, List.getLast?_reverse, hy.1, hy.2, rotate]

theorem division_word {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    ((division rotation).op x y).toWord =
      x.toWord ++ ((rotation (rotation y))⁻¹).toWord ++ x.toWord := by
  have hm := middle_ends hy
  have hr : FreeGroup.IsReduced
      (x.toWord ++ ((rotation (rotation y))⁻¹).toWord ++ x.toWord) := by
    apply List.IsChain.append
    · apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
      simp only [hx.2, hm.1, Option.mem_some_iff]
      rintro a rfl b rfl h
      exact False.elim (by contradiction)
    · exact FreeGroup.isReduced_toWord
    · have hn : ((rotation (rotation y))⁻¹).toWord ≠ [] := by
        intro he
        simpa [he] using hm.2
      rw [List.getLast?_append_of_ne_nil _ hn]
      simp only [hm.2, hx.1, Option.mem_some_iff]
      rintro a rfl b rfl h
      exact False.elim (by contradiction)
  change (x * (rotation (rotation y))⁻¹ * x).toWord = _
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mul,
    (show FreeGroup.IsReduced (x.toWord ++ ((rotation (rotation y))⁻¹).toWord) from
      List.IsChain.left_of_append hr).reduce_eq, hr.reduce_eq]

theorem division_bounded {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    bounded ((division rotation).op x y) := by
  have hn : x.toWord ≠ [] := by
    intro he
    simpa [he] using hx.1
  constructor
  · rw [division_word hx hy, List.append_assoc,
      List.head?_append_of_ne_nil _ hn]
    exact hx.1
  · rw [division_word hx hy, List.getLast?_append_of_ne_nil _ hn]
    exact hx.2

theorem eval_bounded {A : Type} (t : FreeMagma A) (v : A → Carrier)
    (hv : ∀ i, bounded (v i)) :
    bounded (@evalInMagma _ _ (division rotation) v t) := by
  induction t with
  | Leaf i => exact hv i
  | Fork a b ha hb => exact division_bounded ha hb

/-- Even on this one model, no binary term in left division recovers the
original E1525 multiplication. All terms at the first generator still begin
and end there, whereas its original square is the second generator. -/
theorem inverse_not_term (t : FreeMagma (Fin 2)) :
    (termMagma (division rotation) t).op ≠ (source rotation).op := by
  intro he
  have hb : bounded ((termMagma (division rotation) t).op (FreeGroup.of 0)
      (FreeGroup.of 0)) := eval_bounded t _ (fun _ => by simp [bounded])
  rw [he] at hb
  have hs : (source rotation).op (FreeGroup.of 0) (FreeGroup.of 0) = FreeGroup.of 1 := by
    change rotation (FreeGroup.of 0 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 0) = FreeGroup.of 1
    rw [mul_inv_cancel, one_mul]
    rfl
  rw [hs] at hb
  have h := hb.1
  simp [FreeGroup.toWord_of] at h

abbrev Subcarrier := {x : Carrier // bounded x}
@[implicit_reducible] def subDivision : Magma Subcarrier :=
  ⟨fun x y => ⟨(division rotation).op x.1 y.1, division_bounded x.2 y.2⟩⟩

def generator : Subcarrier := ⟨FreeGroup.of 0, by simp [bounded]⟩

theorem sub_eval (t : FreeMagma Nat) (v : Nat → Subcarrier) :
    (@evalInMagma _ _ subDivision v t).val =
      @evalInMagma _ _ (division rotation) (fun i => (v i).val) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change (division rotation).op _ _ = _
    rw [ha, hb]
    rfl

theorem sub_not_leftQuasigroup : ¬ IsSideQuasigroup .left subDivision := by
  intro hQ
  obtain ⟨y, hy⟩ := (hQ generator).2 generator
  have he := congrArg (fun x : Subcarrier => x.val.toWord.length) hy
  change (((division rotation).op generator.val y.val).toWord).length = _ at he
  rw [division_word generator.2 y.2] at he
  simp only [List.length_append, generator, FreeGroup.toWord_of,
    List.length_singleton] at he
  omega

/-- The division image is not closed under submagmas: words beginning and
ending in the first generator form a submagma, but its first row omits that
generator. Therefore not even a set of identities could define this image. -/
theorem no_singleEquation : ¬ SingleEquation .all Law1525 .left := by
  rintro ⟨target, ht⟩
  have hwhole : @satisfies _ Carrier (division rotation) target := by
    apply (ht Carrier (division rotation) trivial).mpr
    exact ⟨source rotation, (@Law1525.models_iff _ (source rotation)).mpr
      (source_law rotation rotation_three), isDivision rotation rotation_three⟩
  have hsub : @satisfies _ Subcarrier subDivision target := by
    intro v
    apply Subtype.val_injective
    rw [sub_eval, sub_eval]
    exact hwhole (fun i => (v i).val)
  exact sub_not_leftQuasigroup
    (characterizes_sideQuasigroup ht Subcarrier subDivision trivial hsub)

end Parastrophes.TrialityCore

namespace Parastrophes.Catalogue
@[parastrophe_result] theorem left_noSingleEquation1525_all :
    ¬ SingleEquation .all Law1525 .left := TrialityCore.no_singleEquation
end Parastrophes.Catalogue

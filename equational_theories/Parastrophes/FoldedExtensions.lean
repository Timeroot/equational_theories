import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All
import Mathlib.Topology.Instances.Real.Lemmas

/-! Infinite collision models obtained by adjoining a right zero to an affine
magma. The new row is a piecewise affine surjection with a collision. -/
namespace Parastrophes.FoldedExtensions

/-- Adjoin a right zero; its row on the old carrier is the specified function. -/
@[implicit_reducible] def extension {G : Type*} (op : G → G → G) (f : G → G) : Magma (Option G) where
  op
  | _, none => none
  | none, some y => some (f y)
  | some x, some y => some (op x y)

theorem equation669 {G : Type*} (op : G → G → G) (f : G → G)
    (h : @Equation669 G ⟨op⟩) (hf : ∀ x, f (op x (f x)) = x) :
    @Equation669 (Option G) (extension op f) := by
  rintro (_ | x) (_ | y)
  · rfl
  · rfl
  · exact congrArg some (hf x).symm
  · exact congrArg some (h x y)

theorem equation1285 {G : Type*} (op : G → G → G) (f : G → G)
    (h : @Equation1285 G ⟨op⟩) (hf : ∀ x, f (op (f x) x) = x) :
    @Equation1285 (Option G) (extension op f) := by
  rintro (_ | x) (_ | y)
  · rfl
  · rfl
  · exact congrArg some (hf x).symm
  · exact congrArg some (h x y)

/-- This extension cannot create a new noninjective row for E1075: the law
forces that row to be an involution. -/
theorem equation1075_involution {G : Type*} (op : G → G → G) (f : G → G)
    (h : @Equation1075 (Option G) (extension op f)) (x : G) :
    f (f x) = x := (Option.some.inj (h (some x) none)).symm

/-- The same obstruction applies to E1278. -/
theorem equation1278_involution {G : Type*} (op : G → G → G) (f : G → G)
    (h : @Equation1278 (Option G) (extension op f)) (x : G) :
    f (f x) = x := (Option.some.inj (h (some x) none)).symm

/-- For E879 the necessary condition also involves the old square map. -/
theorem equation879_square_section {G : Type*} (op : G → G → G) (f : G → G)
    (h : @Equation879 (Option G) (extension op f)) (x : G) :
    f (f (op x x)) = x := (Option.some.inj (h (some x) none)).symm

/-- E464 cannot admit this right-zero extension of a nonempty carrier. -/
theorem not_equation464 {G : Type*} [Nonempty G] (op : G → G → G) (f : G → G) :
    ¬ @Equation464 (Option G) (extension op f) := by
  intro h
  cases h none (some (Classical.arbitrary G))

/-- Move one step towards zero, choosing +1 at zero. -/
def foldInt (x : Int) : Int := if 0 < x then x - 1 else x + 1

theorem foldInt_section (x : Int) : foldInt (2 * x - foldInt x) = x := by
  unfold foldInt
  split_ifs <;> omega

/-- The old rows are reflections; only the new row can have collisions. -/
@[implicit_reducible] def model669 : Magma (Option Int) := extension (fun x y => 2 * x - y) foldInt

theorem model669_law : @Equation669 (Option Int) model669 := by
  apply equation669
  · intro x y
    change x = 2 * y - (2 * x - (2 * (2 * x - y) - x))
    ring
  · exact foldInt_section

theorem model669_idempotent (x : Option Int) : model669.op x x = x := by
  cases x with
  | none => rfl
  | some x => change some (2 * x - x) = some x; congr 1; ring

/-- A positive parameter for the idempotent E1285 affine operation. -/
theorem parameter_exists : ∃ b : Real, 0 < b ∧ b * (1 + b)^2 = 1 := by
  have hc : Continuous (fun b : Real => b * (1 + b)^2) := by fun_prop
  obtain ⟨b, hb, he⟩ := intermediate_value_Icc (by norm_num : (0 : Real) ≤ 1)
    hc.continuousOn (show (1 : Real) ∈ Set.Icc (0 * (1 + 0)^2) (1 * (1 + 1)^2) by norm_num)
  refine ⟨b, ?_, he⟩
  by_contra hn
  have : b = 0 := le_antisymm (le_of_not_gt hn) hb.1
  subst b
  norm_num at he

/-- The two half-lines expand, with overlapping images around zero. -/
noncomputable def foldReal (b x : Real) : Real :=
  if 0 < x then x / b - 1 else x / b + 1

theorem foldReal_section {b : Real} (hb : 0 < b) (x : Real) :
    foldReal b (-b * foldReal b x + (1 + b) * x) = x := by
  have hn : b ≠ 0 := ne_of_gt hb
  by_cases hx : 0 < x
  · have harg : -b * foldReal b x + (1 + b) * x = b * (x + 1) := by
      rw [foldReal, if_pos hx]
      field_simp
      ring
    rw [harg, foldReal, if_pos (mul_pos hb (by linarith))]
    field_simp
    ring
  · have harg : -b * foldReal b x + (1 + b) * x = b * (x - 1) := by
      rw [foldReal, if_neg hx]
      field_simp
      ring
    rw [harg, foldReal, if_neg (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hb (by linarith))))]
    field_simp
    ring

@[implicit_reducible] noncomputable def model1285 (b : Real) : Magma (Option Real) :=
  extension (fun x y => -b * x + (1 + b) * y) (foldReal b)

theorem model1285_law {b : Real} (hb : 0 < b) (he : b * (1 + b)^2 = 1) :
    @Equation1285 (Option Real) (model1285 b) := by
  apply equation1285
  · intro x y
    change x = -b * y + (1 + b) * (-b * (-b * (-b * x + (1 + b) * y) + (1 + b) * x) + (1 + b) * x)
    nlinarith [congrArg (fun t : Real => t * (b * x)) he,
      congrArg (fun t : Real => t * (b * y)) he,
      congrArg (fun t : Real => t * x) he,
      congrArg (fun t : Real => t * y) he]
  · exact foldReal_section hb

theorem model1285_idempotent (b : Real) (x : Option Real) :
    (model1285 b).op x x = x := by
  cases x with
  | none => rfl
  | some x => change some (-b * x + (1 + b) * x) = some x; congr 1; ring

end FoldedExtensions
open FoldedExtensions Law

@[parastrophe_result] theorem Catalogue.not_leftQuasigroup669_all :
    ¬ SideQuasigroupLaw .all Law669 .left := by
  intro h
  have hq := h (Option Int) model669 trivial
    ((@Law669.models_iff _ model669).mpr model669_law)
  have hc : model669.op none (some 1) = model669.op none (some (-1)) := by decide
  have he := (hq none).1 hc
  cases he

@[parastrophe_result] theorem Catalogue.not_leftQuasigroup1285_all :
    ¬ SideQuasigroupLaw .all Law1285 .left := by
  obtain ⟨b, hb, he⟩ := parameter_exists
  intro h
  have hq := h (Option Real) (model1285 b) trivial
    ((@Law1285.models_iff _ (model1285 b)).mpr (model1285_law hb he))
  have hn : b ≠ 0 := ne_of_gt hb
  have hc : (model1285 b).op none (some b) = (model1285 b).op none (some (-b)) := by
    change some (foldReal b b) = some (foldReal b (-b))
    simp [foldReal, hb, hn, not_lt.mpr (le_of_lt (neg_neg_of_pos hb))]
  have hh := Option.some.inj ((hq none).1 hc)
  linarith

end Parastrophes

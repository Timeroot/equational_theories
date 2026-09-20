import equational_theories.Definability.InvariantFamilyCounting

/-! A complete family preserved by translations and a noninvertible projection. -/
open Law Law.MagmaLaw
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionEndomorphism4
def addData : Array (Array (Fin 4)) := #[#[0, 1, 2, 3], #[1, 0, 3, 2], #[2, 3, 0, 1], #[3, 2, 1, 0]]
def add (x y : Fin 4) : Fin 4 := (addData.getD x.val #[]).getD y.val 0
def projectionData : Array (Fin 4) := #[0, 1, 0, 1]
def projection (x : Fin 4) : Fin 4 := projectionData.getD x.val 0
def functionData : Array (Array (Fin 4)) := #[#[0, 0, 0, 0], #[0, 0, 0, 2], #[0, 0, 2, 0], #[0, 0, 2, 2], #[0, 1, 0, 1], #[0, 1, 0, 3], #[0, 1, 2, 1], #[0, 1, 2, 3], #[1, 0, 1, 0], #[1, 0, 1, 2], #[1, 0, 3, 0], #[1, 0, 3, 2], #[1, 1, 1, 1], #[1, 1, 1, 3], #[1, 1, 3, 1], #[1, 1, 3, 3]]
def function (i : Fin 16) (x : Fin 4) : Fin 4 :=
  (functionData.getD i.val #[]).getD x.val 0
def gen (i : Fin 5) (x : Fin 4) : Fin 4 :=
  if h : i.val < 4 then add ⟨i.val, h⟩ x else projection x
@[implicit_reducible] def fam (i : Fin 16) : Magma (Fin 4) :=
  ⟨fun x y => add x (function i (add x y))⟩

theorem add_zero : ∀ x, add x 0 = x := by decide
theorem add_cancel : ∀ x y, add x (add x y) = y := by decide
theorem projection_zero : projection 0 = 0 := by decide
theorem gen_translation (x : Fin 4) : gen x.castSucc = add x := by
  funext y
  simp [gen, x.isLt]

theorem function_coverage : ∀ f : Fin 4 → Fin 4,
    (∀ x, projection (f x) = f (projection x)) → ∃ i, function i = f := by native_decide

theorem coverage (N : Magma (Fin 4)) (hg : ∀ i, N.IsEndo (gen i)) :
    ∃ i, fam i = N := by
  let f : Fin 4 → Fin 4 := fun x => N.op 0 x
  have hp : ∀ x, projection (f x) = f (projection x) := by
    intro x
    have ht := hg 4 0 x
    change projection (N.op 0 x) = N.op (projection 0) (projection x) at ht
    simpa only [projection_zero] using ht
  obtain ⟨i, hi⟩ := function_coverage f hp
  refine ⟨i, ?_⟩
  apply congrArg Magma.mk
  funext x y
  change add x (function i (add x y)) = N.op x y
  rw [hi]
  have ht := hg x.castSucc 0 (add x y)
  rw [gen_translation] at ht
  simpa only [add_zero, add_cancel] using ht

theorem family_injective : Function.Injective (fun i : Fin 16 => (fam i).op) := by native_decide
theorem family_generators : ∀ i j, (fam i).IsEndo (gen j) := by native_decide

private def test153 (p : Fin 16) : Prop := ∀ x y : Fin 4, x = ((fam p).op ((fam p).op x x) ((fam p).op y x))
private instance (p : Fin 16) : Decidable (test153 p) := by unfold test153; infer_instance
private theorem count153 : Fintype.card {p : Fin 16 // test153 p} = 14 := by native_decide

private def test1644 (p : Fin 16) : Prop := ∀ x y : Fin 4, x = ((fam p).op ((fam p).op x y) ((fam p).op ((fam p).op x x) x))
private instance (p : Fin 16) : Decidable (test1644 p) := by unfold test1644; infer_instance
private theorem count1644 : Fintype.card {p : Fin 16 // test1644 p} = 14 := by native_decide

private def test3306 (p : Fin 16) : Prop := ∀ x y : Fin 4, ((fam p).op x y) = ((fam p).op x ((fam p).op x ((fam p).op x y)))
private instance (p : Fin 16) : Decidable (test3306 p) := by unfold test3306; infer_instance
private theorem count3306 : Fintype.card {p : Fin 16 // test3306 p} = 12 := by native_decide

end Magma.ProjectionEndomorphism4

open Magma.ProjectionEndomorphism4

theorem Equation3306_not_termStructuralFromFin_Equation153_projectionEndomorphism4 : ¬ Law3306.TermStructuralFromFin Law153 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin gen fam family_injective
    coverage family_generators (test153) (test3306)
  · intro p hp
    exact (@Law153.models_iff (Fin 4) (fam p)).mpr hp
  · intro p hp
    exact (@Law3306.models_iff (Fin 4) (fam p)).mp hp
  · rw [count153, count3306]
    decide

/-- info: 'Equation3306_not_termStructuralFromFin_Equation153_projectionEndomorphism4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 family_generators._native.native_decide.ax_1_1,
 family_injective._native.native_decide.ax_1_1,
 function_coverage._native.native_decide.ax_1_1,
 count153._native.native_decide.ax_1_1,
 count3306._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3306_not_termStructuralFromFin_Equation153_projectionEndomorphism4

theorem Equation3306_not_termStructuralFromFin_Equation1644_projectionEndomorphism4 : ¬ Law3306.TermStructuralFromFin Law1644 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin gen fam family_injective
    coverage family_generators (test1644) (test3306)
  · intro p hp
    exact (@Law1644.models_iff (Fin 4) (fam p)).mpr hp
  · intro p hp
    exact (@Law3306.models_iff (Fin 4) (fam p)).mp hp
  · rw [count1644, count3306]
    decide

/-- info: 'Equation3306_not_termStructuralFromFin_Equation1644_projectionEndomorphism4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 family_generators._native.native_decide.ax_1_1,
 family_injective._native.native_decide.ax_1_1,
 function_coverage._native.native_decide.ax_1_1,
 count1644._native.native_decide.ax_1_1,
 count3306._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3306_not_termStructuralFromFin_Equation1644_projectionEndomorphism4


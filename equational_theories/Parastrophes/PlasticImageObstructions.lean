import equational_theories.Parastrophes.AffineImageObstructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Cubic integer matrices give finite division-image obstructions. The matrix
T satisfies T³=T+1. Evaluating it at the positive real root makes the left
division coefficients positive, so every image identity also holds in Boolean OR. -/
namespace Parastrophes.PlasticImage
open Law FreeMagma AffineImage

variable {R : Type*} [CommRing R]

def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0 + x 2, x 1]
def Ti (x : Fin 3 → R) : Fin 3 → R := ![x 1 - x 0, x 2, x 0]

theorem T_Ti (x : Fin 3 → R) : T (Ti x) = x := by
  ext i; fin_cases i <;> simp [T, Ti]

@[implicit_reducible] def m115 : Magma (Fin 3 → R) := ⟨fun x y => -T (T x) + T y⟩
@[implicit_reducible] def d115 : Magma (Fin 3 → R) := ⟨fun x y => T x + Ti y⟩
@[implicit_reducible] def m222 : Magma (Fin 3 → R) := ⟨fun x y => -Ti x + T (T y)⟩
@[implicit_reducible] def d222 : Magma (Fin 3 → R) := ⟨fun x y => Ti (Ti (Ti x)) + Ti (Ti y)⟩

@[simp] theorem m115_op (x y : Fin 3 → R) : (m115 (R := R)).op x y = -T (T x) + T y := rfl
@[simp] theorem d115_op (x y : Fin 3 → R) : (d115 (R := R)).op x y = T x + Ti y := rfl
@[simp] theorem m222_op (x y : Fin 3 → R) : (m222 (R := R)).op x y = -Ti x + T (T y) := rfl
@[simp] theorem d222_op (x y : Fin 3 → R) : (d222 (R := R)).op x y = Ti (Ti (Ti x)) + Ti (Ti y) := rfl

theorem division115 : IsDivision .left (m115 (R := R)) d115 := by
  constructor <;> intro x y <;> simp only [m115_op, d115_op] <;> ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

theorem division222 : IsDivision .left (m222 (R := R)) d222 := by
  constructor <;> intro x y <;> simp only [m222_op, d222_op] <;> ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

theorem equation115 : @Equation115 _ (m115 (R := R)) := by
  intro x y; simp only [m115_op]; ext i; fin_cases i <;> simp [T] <;> ring

theorem equation118 : @Equation118 _ (m222 (R := R)) := by
  intro x y; simp only [m222_op]; ext i; fin_cases i <;> simp [T, Ti] <;> ring

theorem equation222 : @Equation222 _ (m222 (R := R)) := by
  intro x y; simp only [m222_op]; ext i; fin_cases i <;> simp [T, Ti] <;> ring

@[implicit_reducible] def m667 : Magma (Fin 3 → R) := ⟨fun x y => -T (T (T x)) + T y⟩
@[implicit_reducible] def d667 : Magma (Fin 3 → R) := ⟨fun x y => T (T x) + Ti y⟩
@[simp] theorem m667_op (x y : Fin 3 → R) : (m667 (R := R)).op x y = -T (T (T x)) + T y := rfl
@[simp] theorem d667_op (x y : Fin 3 → R) : (d667 (R := R)).op x y = T (T x) + Ti y := rfl

theorem division667 : IsDivision .left (m667 (R := R)) d667 := by
  constructor <;> intro x y <;> simp only [m667_op, d667_op] <;>
    ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

@[implicit_reducible] def m271 : Magma (Fin 3 → R) := ⟨fun x y => -T x + T y + y⟩
@[implicit_reducible] def d271 : Magma (Fin 3 → R) := ⟨fun x y => Ti (Ti x) + Ti (Ti (Ti y))⟩
@[simp] theorem m271_op (x y : Fin 3 → R) : (m271 (R := R)).op x y = -T x + T y + y := rfl
@[simp] theorem d271_op (x y : Fin 3 → R) : (d271 (R := R)).op x y = Ti (Ti x) + Ti (Ti (Ti y)) := rfl

theorem division271 : IsDivision .left (m271 (R := R)) d271 := by
  constructor <;> intro x y <;> simp only [m271_op, d271_op] <;>
    ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

@[implicit_reducible] def m1119 : Magma (Fin 3 → R) := ⟨fun x y => x - T x + T y⟩
@[implicit_reducible] def d1119 : Magma (Fin 3 → R) := ⟨fun x y => x - Ti x + Ti y⟩
@[simp] theorem m1119_op (x y : Fin 3 → R) : (m1119 (R := R)).op x y = x - T x + T y := rfl
@[simp] theorem d1119_op (x y : Fin 3 → R) : (d1119 (R := R)).op x y = x - Ti x + Ti y := rfl

theorem division1119 : IsDivision .left (m1119 (R := R)) d1119 := by
  constructor <;> intro x y <;> simp only [m1119_op, d1119_op] <;>
    ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : t^3 = t+1) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk, T, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Int.cast_add]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem project_Ti {t : Real} (ht : t^3 = t+1) (x : Fin 3 → Int) :
    project t (Ti x) = (t^2-1) * project t x := by
  have hinv : (t^2-1)*t = 1 := by nlinarith [ht]
  calc
    project t (Ti x) = ((t^2-1)*t) * project t (Ti x) := by rw [hinv, one_mul]
    _ = (t^2-1) * (t * project t (Ti x)) := mul_assoc _ _ _
    _ = (t^2-1) * project t x := by rw [← project_T ht, T_Ti]

private theorem positive_root : ∃ t : Real, 1 < t ∧ t^3 = t+1 := by
  have hc : Continuous (fun t : Real => t^3-t-1) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (1^3-1-1) (2^3-2-1) by norm_num)
  refine ⟨t, ?_, by linarith⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction115 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m115 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left (d115 (R := Int)) (fun n => d115 (R := ZMod n))
    ?_ ?_ (project t) sample (a := t) (b := t^2-1) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [d115_op]; ext i; fin_cases i <;> simp [reduce, T, Ti]
  · intro n hn; exact ⟨m115, hL n hn, division115⟩
  · linarith
  · nlinarith
  · intro x y
    change project t (T x + Ti y) = _
    rw [map_add, project_T he, project_Ti he]
  · simp [project, sample]
  · simp [project, sample]

theorem obstruction222 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m222 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t^2-1 := by nlinarith
  refine no_singleEquation_left (d222 (R := Int)) (fun n => d222 (R := ZMod n))
    ?_ ?_ (project t) sample (a := (t^2-1)^3) (b := (t^2-1)^2) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [d222_op]; ext i; fin_cases i <;> simp [reduce, Ti]
  · intro n hn; exact ⟨m222, hL n hn, division222⟩
  · exact pow_pos hp _
  · exact pow_pos hp _
  · intro x y
    change project t (Ti (Ti (Ti x)) + Ti (Ti y)) = _
    simp only [map_add, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

theorem obstruction667 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m667 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t^2-1 := by nlinarith
  refine no_singleEquation_left (d667 (R := Int)) (fun n => d667 (R := ZMod n))
    ?_ ?_ (project t) sample (a := t^2) (b := t^2-1) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [d667_op]; ext i; fin_cases i <;> simp [reduce, T, Ti]
  · intro n hn; exact ⟨m667, hL n hn, division667⟩
  · exact pow_pos (by linarith : 0 < t) _
  · exact hp
  · intro x y
    change project t (T (T x) + Ti y) = _
    simp only [map_add, project_T he, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

theorem obstruction271 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m271 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t^2-1 := by nlinarith
  refine no_singleEquation_left (d271 (R := Int)) (fun n => d271 (R := ZMod n))
    ?_ ?_ (project t) sample (a := (t^2-1)^2) (b := (t^2-1)^3) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [d271_op]; ext i; fin_cases i <;> simp [reduce, Ti]
  · intro n hn; exact ⟨m271, hL n hn, division271⟩
  · exact pow_pos hp _
  · exact pow_pos hp _
  · intro x y
    change project t (Ti (Ti x) + Ti (Ti (Ti y))) = _
    simp only [map_add, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

theorem obstruction1119 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m1119 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t^2-1 := by nlinarith
  refine no_singleEquation_left (d1119 (R := Int)) (fun n => d1119 (R := ZMod n))
    ?_ ?_ (project t) sample (a := 2-t^2) (b := t^2-1) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [d1119_op]; ext i; fin_cases i <;> simp [reduce, Ti]
  · intro n hn; exact ⟨m1119, hL n hn, division1119⟩
  · have hinv : (t^2-1)*t = 1 := by nlinarith [he]
    nlinarith [mul_pos hp (show 0 < t-1 by linarith)]
  · exact hp
  · intro x y
    change project t (x - Ti x + Ti y) = _
    simp only [map_add, map_sub, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Parastrophes.PlasticImage

namespace Parastrophes.Catalogue
open PlasticImage

/-- Cubic matrix reductions obstruct a single identity for E115's finite left image. -/
@[parastrophe_result] theorem left_noSingleEquation115_fin :
    ¬ SingleEquation .fin Law115 .left :=
  obstruction115 (fun _ _ => (@Law115.models_iff _ (m115 (R := ZMod _))).mpr equation115)

/-- An idempotent cubic matrix family supplies the E118 obstruction. -/
@[parastrophe_result] theorem left_noSingleEquation118_fin :
    ¬ SingleEquation .fin Law118 .left :=
  obstruction222 (fun _ _ => (@Law118.models_iff _ (m222 (R := ZMod _))).mpr equation118)

/-- This also refutes E125's right-image characterization, by duality. -/
@[parastrophe_result] theorem left_noSingleEquation222_fin :
    ¬ SingleEquation .fin Law222 .left :=
  obstruction222 (fun _ _ => (@Law222.models_iff _ (m222 (R := ZMod _))).mpr equation222)

end Parastrophes.Catalogue

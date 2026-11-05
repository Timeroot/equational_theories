import equational_theories.Parastrophes.AffineImageObstructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Quadratic integer matrices give finite division-image obstructions. The
matrix T satisfies T²=T+1; its positive real root makes both division
coefficients positive. The general obstruction then applies to Boolean join. -/
namespace Parastrophes.GoldenImage
open Law FreeMagma AffineImage

variable {R : Type*} [CommRing R]

def T (x : Fin 2 → R) : Fin 2 → R := ![x 1, x 0 + x 1]
def Ti (x : Fin 2 → R) : Fin 2 → R := ![x 1 - x 0, x 0]

theorem T_Ti (x : Fin 2 → R) : T (Ti x) = x := by
  ext i; fin_cases i <;> simp [T, Ti]

@[implicit_reducible] def source : Magma (Fin 2 → R) := ⟨fun x y => -Ti x + T y⟩
@[implicit_reducible] def division : Magma (Fin 2 → R) := ⟨fun x y => Ti (Ti x) + Ti y⟩

@[simp] theorem source_op (x y : Fin 2 → R) :
    (source (R := R)).op x y = -Ti x + T y := rfl
@[simp] theorem division_op (x y : Fin 2 → R) :
    (division (R := R)).op x y = Ti (Ti x) + Ti y := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

theorem equation124 : @Equation124 _ (source (R := R)) := by
  intro x y; simp only [source_op]; ext i; fin_cases i <;> simp [T, Ti] <;> ring

@[implicit_reducible] def m679 : Magma (Fin 2 → R) := ⟨fun x y => -(x+x) + T y⟩
@[implicit_reducible] def d679 : Magma (Fin 2 → R) := ⟨fun x y => Ti (x+x) + Ti y⟩
@[simp] theorem m679_op (x y : Fin 2 → R) : (m679 (R := R)).op x y = -(x+x) + T y := rfl
@[simp] theorem d679_op (x y : Fin 2 → R) : (d679 (R := R)).op x y = Ti (x+x) + Ti y := rfl

theorem division679 : IsDivision .left (m679 (R := R)) d679 := by
  constructor <;> intro x y <;> simp only [m679_op, d679_op] <;>
    ext i <;> fin_cases i <;> simp [T, Ti] <;> ring

private def project (t : Real) : (Fin 2 → Int) →+ Real where
  toFun x := (x 0 : Real) + t * (x 1 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : t^2 = t+1) (x : Fin 2 → Int) :
    project t (T x) = t * project t x := by
  simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk, T, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_add]
  nlinarith [congrArg (fun z : Real => z * (x 1 : Real)) ht]

private theorem project_Ti {t : Real} (ht : t^2 = t+1) (x : Fin 2 → Int) :
    project t (Ti x) = (t-1) * project t x := by
  have hinv : (t-1)*t = 1 := by nlinarith [ht]
  calc
    project t (Ti x) = ((t-1)*t) * project t (Ti x) := by rw [hinv, one_mul]
    _ = (t-1) * (t * project t (Ti x)) := mul_assoc _ _ _
    _ = (t-1) * project t x := by rw [← project_T ht, T_Ti]

private theorem positive_root : ∃ t : Real, 1 < t ∧ t^2 = t+1 := by
  have hc : Continuous (fun t : Real => t^2-t-1) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (1^2-1-1) (2^2-2-1) by norm_num)
  refine ⟨t, ?_, by linarith⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 2 → Int := ![if b then 1 else 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t-1 := by linarith
  refine no_singleEquation_left (division (R := Int)) (fun n => division (R := ZMod n))
    ?_ ?_ (project t) sample (a := (t-1)^2) (b := t-1) ?_ hp ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, Ti]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · exact pow_pos hp _
  · intro x y
    change project t (Ti (Ti x) + Ti y) = _
    simp only [map_add, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

theorem obstruction679 {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (m679 (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  have hp : 0 < t-1 := by linarith
  refine no_singleEquation_left (d679 (R := Int)) (fun n => d679 (R := ZMod n))
    ?_ ?_ (project t) sample (a := 2*(t-1)) (b := t-1) ?_ hp ?_ ?_ ?_
  · intro n x y; simp only [d679_op]; ext i; fin_cases i <;> simp [reduce, Ti]
  · intro n hn; exact ⟨m679, hL n hn, division679⟩
  · positivity
  · intro x y
    change project t (Ti (x+x) + Ti y) = _
    simp only [map_add, project_Ti he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Parastrophes.GoldenImage

namespace Parastrophes.Catalogue

/-- The golden-ratio matrix family excludes every identity for E124's finite left image. -/
@[parastrophe_result] theorem left_noSingleEquation124_fin :
    ¬ SingleEquation .fin Law124 .left :=
  GoldenImage.obstruction (fun _ _ =>
    (@Law124.models_iff _ (GoldenImage.source (R := ZMod _))).mpr GoldenImage.equation124)

end Parastrophes.Catalogue

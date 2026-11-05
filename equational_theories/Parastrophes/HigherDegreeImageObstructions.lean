import equational_theories.Parastrophes.AffineImageObstructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Instances.Real.Lemmas

/-! Further finite division-image obstructions from integral companion matrices.
Each block records a monic polynomial, its companion matrix, source and division
operations, and a positive real evaluation. Coordinate proofs are symbolic ring
calculations, not enumeration over finite magmas. -/
namespace Parastrophes
open Law FreeMagma AffineImage

namespace Companion670
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^4 - 2 * x^3 + x - 1 = 0`. -/
def T (x : Fin 4 → R) : Fin 4 → R := ![x 3, x 0 - x 3, x 1, x 2 + x 3 + x 3]

@[implicit_reducible] def source : Magma (Fin 4 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 4 → R) :=
  ⟨fun x y => (T (T x) + T (T x) - T (T (T x))) + (y - T (T y) - T (T y) + T (T (T y)))⟩
@[simp] theorem source_op (x y : Fin 4 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 4 → R) :
    (division (R := R)).op x y = (T (T x) + T (T x) - T (T (T x))) + (y - T (T y) - T (T y) + T (T (T y))) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 4 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real) + t^3 * (x 3 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 + t - t^3 - t^3 + t^4 = 0) (x : Fin 4 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 3 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 + t - t^3 - t^3 + t^4 = 0 := by
  have hc : Continuous (fun t : Real => -1 + t - t^3 - t^3 + t^4) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 + 1 - 1^3 - 1^3 + 1^4) (-1 + 2 - 2^3 - 2^3 + 2^4) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 4 → Int := ![if b then 1 else 0, 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion670

/-- The degree-4 matrix family proves the finite E670 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation670_fin :
    ¬ SingleEquation .fin Law670 .left := by
  apply Companion670.obstruction
  intro n _
  apply (@Law670.models_iff _ (Companion670.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion670.source_op]
  ext i; fin_cases i <;> simp [Companion670.T] <;> ring

namespace Companion676
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^3 - x^2 - 1 = 0`. -/
def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0, x 1 + x 2]

@[implicit_reducible] def source : Magma (Fin 3 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 3 → R) :=
  ⟨fun x y => (x + T x - T (T x)) + (-T y + T (T y))⟩
@[simp] theorem source_op (x y : Fin 3 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = (x + T x - T (T x)) + (-T y + T (T y)) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t^2 + t^3 = 0) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t^2 + t^3 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t^2 + t^3) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 1^2 + 1^3) (-1 - 2^2 + 2^3) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion676

/-- The degree-3 matrix family proves the finite E676 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation676_fin :
    ¬ SingleEquation .fin Law676 .left := by
  apply Companion676.obstruction
  intro n _
  apply (@Law676.models_iff _ (Companion676.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion676.source_op]
  ext i; fin_cases i <;> simp [Companion676.T] <;> ring

/-- The degree-3 matrix family proves the finite E1285 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation1285_fin :
    ¬ SingleEquation .fin Law1285 .left := by
  apply Companion676.obstruction
  intro n _
  apply (@Law1285.models_iff _ (Companion676.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion676.source_op]
  ext i; fin_cases i <;> simp [Companion676.T] <;> ring

namespace Companion870
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^3 - x^2 - 1 = 0`. -/
def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0, x 1 + x 2]

@[implicit_reducible] def source : Magma (Fin 3 → R) :=
  ⟨fun x y => (-x - T (T x)) + T y⟩
@[implicit_reducible] def division : Magma (Fin 3 → R) :=
  ⟨fun x y => (T (T x)) + (-T y + T (T y))⟩
@[simp] theorem source_op (x y : Fin 3 → R) :
    (source (R := R)).op x y = (-x - T (T x)) + T y := rfl
@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = (T (T x)) + (-T y + T (T y)) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t^2 + t^3 = 0) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t^2 + t^3 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t^2 + t^3) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 1^2 + 1^3) (-1 - 2^2 + 2^3) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := -1 - t^2) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · nlinarith [sq_nonneg t]
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, map_neg, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion870

/-- The degree-3 matrix family proves the finite E870 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation870_fin :
    ¬ SingleEquation .fin Law870 .left := by
  apply Companion870.obstruction
  intro n _
  apply (@Law870.models_iff _ (Companion870.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion870.source_op]
  ext i; fin_cases i <;> simp [Companion870.T] <;> ring

namespace Companion1083
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^3 - x^2 - 1 = 0`. -/
def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0, x 1 + x 2]

@[implicit_reducible] def source : Magma (Fin 3 → R) :=
  ⟨fun x y => (-T x) + (-T y + T (T y))⟩
@[implicit_reducible] def division : Magma (Fin 3 → R) :=
  ⟨fun x y => (T (T x)) + T y⟩
@[simp] theorem source_op (x y : Fin 3 → R) :
    (source (R := R)).op x y = (-T x) + (-T y + T (T y)) := rfl
@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = (T (T x)) + T y := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t^2 + t^3 = 0) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t^2 + t^3 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t^2 + t^3) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 1^2 + 1^3) (-1 - 2^2 + 2^3) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := -t) (b := -t + t^2) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · nlinarith
  · intro x y
    simp only [source_op, map_add, map_neg, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion1083

/-- The degree-3 matrix family proves the finite E1083 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation1083_fin :
    ¬ SingleEquation .fin Law1083 .left := by
  apply Companion1083.obstruction
  intro n _
  apply (@Law1083.models_iff _ (Companion1083.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1083.source_op]
  ext i; fin_cases i <;> simp [Companion1083.T] <;> ring

namespace Companion713
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^3 - x^2 - x - 1 = 0`. -/
def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0 + x 2, x 1 + x 2]

@[implicit_reducible] def source : Magma (Fin 3 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 3 → R) :=
  ⟨fun x y => (x + x + T x - T (T x)) + (-y - T y + T (T y))⟩
@[simp] theorem source_op (x y : Fin 3 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = (x + x + T x - T (T x)) + (-y - T y + T (T y)) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t - t^2 + t^3 = 0) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t - t^2 + t^3 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t - t^2 + t^3) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 1 - 1^2 + 1^3) (-1 - 2 - 2^2 + 2^3) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion713

/-- The degree-3 matrix family proves the finite E713 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation713_fin :
    ¬ SingleEquation .fin Law713 .left := by
  apply Companion713.obstruction
  intro n _
  apply (@Law713.models_iff _ (Companion713.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion713.source_op]
  ext i; fin_cases i <;> simp [Companion713.T] <;> ring

namespace Companion1288
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^3 - 2 * x^2 - 1 = 0`. -/
def T (x : Fin 3 → R) : Fin 3 → R := ![x 2, x 0, x 1 + x 2 + x 2]

@[implicit_reducible] def source : Magma (Fin 3 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 3 → R) :=
  ⟨fun x y => (x + T x + T x - T (T x)) + (-T y - T y + T (T y))⟩
@[simp] theorem source_op (x y : Fin 3 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = (x + T x + T x - T (T x)) + (-T y - T y + T (T y)) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 3 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t^2 - t^2 + t^3 = 0) (x : Fin 3 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 2 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t^2 - t^2 + t^3 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t^2 - t^2 + t^3) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (2 : Real) ≤ 3)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 2^2 - 2^2 + 2^3) (-1 - 3^2 - 3^2 + 3^3) by norm_num)
  exact ⟨t, by linarith [ht.1], he⟩

private def sample (b : Bool) : Fin 3 → Int := ![if b then 1 else 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion1288

/-- The degree-3 matrix family proves the finite E1288 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation1288_fin :
    ¬ SingleEquation .fin Law1288 .left := by
  apply Companion1288.obstruction
  intro n _
  apply (@Law1288.models_iff _ (Companion1288.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1288.source_op]
  ext i; fin_cases i <;> simp [Companion1288.T] <;> ring

namespace Companion1076
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^4 - x^3 - x^2 + x - 1 = 0`. -/
def T (x : Fin 4 → R) : Fin 4 → R := ![x 3, x 0 - x 3, x 1 + x 3, x 2 + x 3]

@[implicit_reducible] def source : Magma (Fin 4 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 4 → R) :=
  ⟨fun x y => (T x + T (T x) - T (T (T x))) + (y - T y - T (T y) + T (T (T y)))⟩
@[simp] theorem source_op (x y : Fin 4 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 4 → R) :
    (division (R := R)).op x y = (T x + T (T x) - T (T (T x))) + (y - T y - T (T y) + T (T (T y))) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 4 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real) + t^3 * (x 3 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 + t - t^2 - t^3 + t^4 = 0) (x : Fin 4 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 3 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 + t - t^2 - t^3 + t^4 = 0 := by
  have hc : Continuous (fun t : Real => -1 + t - t^2 - t^3 + t^4) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 + 1 - 1^2 - 1^3 + 1^4) (-1 + 2 - 2^2 - 2^3 + 2^4) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 4 → Int := ![if b then 1 else 0, 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion1076

/-- The degree-4 matrix family proves the finite E1076 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation1076_fin :
    ¬ SingleEquation .fin Law1076 .left := by
  apply Companion1076.obstruction
  intro n _
  apply (@Law1076.models_iff _ (Companion1076.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1076.source_op]
  ext i; fin_cases i <;> simp [Companion1076.T] <;> ring

/-- The degree-4 matrix family proves the finite E2294 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation2294_fin :
    ¬ SingleEquation .fin Law2294 .left := by
  apply Companion1076.obstruction
  intro n _
  apply (@Law2294.models_iff _ (Companion1076.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1076.source_op]
  ext i; fin_cases i <;> simp [Companion1076.T] <;> ring

namespace Companion1313
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^4 - 3 * x^3 + 2 * x^2 - 1 = 0`. -/
def T (x : Fin 4 → R) : Fin 4 → R := ![x 3, x 0, x 1 - x 3 - x 3, x 2 + x 3 + x 3 + x 3]

@[implicit_reducible] def source : Magma (Fin 4 → R) :=
  ⟨fun x y => (x - T x) + T y⟩
@[implicit_reducible] def division : Magma (Fin 4 → R) :=
  ⟨fun x y => (x - T x - T x + T (T x) + T (T x) + T (T x) - T (T (T x))) + (T y + T y - T (T y) - T (T y) - T (T y) + T (T (T y)))⟩
@[simp] theorem source_op (x y : Fin 4 → R) :
    (source (R := R)).op x y = (x - T x) + T y := rfl
@[simp] theorem division_op (x y : Fin 4 → R) :
    (division (R := R)).op x y = (x - T x - T x + T (T x) + T (T x) + T (T x) - T (T (T x))) + (T y + T y - T (T y) - T (T y) - T (T y) + T (T (T y))) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 4 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real) + t^3 * (x 3 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 + t^2 + t^2 - t^3 - t^3 - t^3 + t^4 = 0) (x : Fin 4 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 3 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 + t^2 + t^2 - t^3 - t^3 - t^3 + t^4 = 0 := by
  have hc : Continuous (fun t : Real => -1 + t^2 + t^2 - t^3 - t^3 - t^3 + t^4) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (2 : Real) ≤ 3)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 + 2^2 + 2^2 - 2^3 - 2^3 - 2^3 + 2^4) (-1 + 3^2 + 3^2 - 3^3 - 3^3 - 3^3 + 3^4) by norm_num)
  exact ⟨t, by linarith [ht.1], he⟩

private def sample (b : Bool) : Fin 4 → Int := ![if b then 1 else 0, 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := 1 - t) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · linarith
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion1313

/-- The degree-4 matrix family proves the finite E1313 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation1313_fin :
    ¬ SingleEquation .fin Law1313 .left := by
  apply Companion1313.obstruction
  intro n _
  apply (@Law1313.models_iff _ (Companion1313.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1313.source_op]
  ext i; fin_cases i <;> simp [Companion1313.T] <;> ring

/-- The degree-4 matrix family proves the finite E2531 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation2531_fin :
    ¬ SingleEquation .fin Law2531 .left := by
  apply Companion1313.obstruction
  intro n _
  apply (@Law2531.models_iff _ (Companion1313.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion1313.source_op]
  ext i; fin_cases i <;> simp [Companion1313.T] <;> ring

namespace Companion704
variable {R : Type*} [CommRing R]

/-- Companion matrix for `x^5 - x^3 - 2 * x^2 - 2 * x - 1 = 0`. -/
def T (x : Fin 5 → R) : Fin 5 → R := ![x 4, x 0 + x 4 + x 4, x 1 + x 4 + x 4, x 2 + x 4, x 3]

@[implicit_reducible] def source : Magma (Fin 5 → R) :=
  ⟨fun x y => (-x - T x - T (T x) - T (T (T x)) + T (T (T (T x)))) + T y⟩
@[implicit_reducible] def division : Magma (Fin 5 → R) :=
  ⟨fun x y => (-x - T x - T (T (T x)) + T (T (T (T x)))) + (-y - y - T y - T y - T (T y) + T (T (T (T y))))⟩
@[simp] theorem source_op (x y : Fin 5 → R) :
    (source (R := R)).op x y = (-x - T x - T (T x) - T (T (T x)) + T (T (T (T x)))) + T y := rfl
@[simp] theorem division_op (x y : Fin 5 → R) :
    (division (R := R)).op x y = (-x - T x - T (T (T x)) + T (T (T (T x)))) + (-y - y - T y - T y - T (T y) + T (T (T (T y)))) := rfl

theorem isDivision : IsDivision .left (source (R := R)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;>
    ext i <;> fin_cases i <;> simp [T] <;> ring

private def project (t : Real) : (Fin 5 → Int) →+ Real where
  toFun x := (x 0 : Real) + t^1 * (x 1 : Real) + t^2 * (x 2 : Real) + t^3 * (x 3 : Real) + t^4 * (x 4 : Real)
  map_zero' := by simp
  map_add' := by intros; simp; ring

private theorem project_T {t : Real} (ht : -1 - t - t - t^2 - t^2 - t^3 + t^5 = 0) (x : Fin 5 → Int) :
    project t (T x) = t * project t x := by
  simp [project, T]
  nlinarith [congrArg (fun z : Real => z * (x 4 : Real)) ht]

private theorem positive_root : ∃ t : Real, 1 < t ∧ -1 - t - t - t^2 - t^2 - t^3 + t^5 = 0 := by
  have hc : Continuous (fun t : Real => -1 - t - t - t^2 - t^2 - t^3 + t^5) := by fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
    hc.continuousOn (show (0 : Real) ∈ Set.Icc (-1 - 1 - 1 - 1^2 - 1^2 - 1^3 + 1^5) (-1 - 2 - 2 - 2^2 - 2^2 - 2^3 + 2^5) by norm_num)
  refine ⟨t, ?_, he⟩
  by_contra h
  have hh : t = 1 := le_antisymm (le_of_not_gt h) ht.1
  subst t
  norm_num at he

private def sample (b : Bool) : Fin 5 → Int := ![if b then 1 else 0, 0, 0, 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (R := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  obtain ⟨t, ht, he⟩ := positive_root
  refine no_singleEquation_left_of_source (source (R := Int)) division
    (fun n => division (R := ZMod n)) ?_ ?_ isDivision (project t) sample
    (a := -1 - t - t^2 - t^3 + t^4) (b := t) ?_ ?_ ?_ ?_ ?_
  · intro n x y; simp only [division_op]; ext i; fin_cases i <;> simp [reduce, T]
  · intro n hn; exact ⟨source, hL n hn, isDivision⟩
  · have heq : (t + 1) * (-1 - t - t^2 - t^3 + t^4) = -t^3 := by nlinarith [he]
    have ht3 : 0 < t^3 := pow_pos (by linarith) _
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ t + 1 by linarith) (le_of_not_gt hn)
    nlinarith [hp]
  · linarith
  · intro x y
    simp only [source_op, map_add, map_sub, map_neg, project_T he]
    ring
  · simp [project, sample]
  · simp [project, sample]

end Companion704

/-- The degree-5 matrix family proves the finite E704 left image is not defined by any identity. -/
@[parastrophe_result] theorem Catalogue.left_noSingleEquation704_fin :
    ¬ SingleEquation .fin Law704 .left := by
  apply Companion704.obstruction
  intro n _
  apply (@Law704.models_iff _ (Companion704.source (R := ZMod n))).mpr
  intro x y
  simp only [Companion704.source_op]
  ext i; fin_cases i <;> simp [Companion704.T] <;> ring

end Parastrophes

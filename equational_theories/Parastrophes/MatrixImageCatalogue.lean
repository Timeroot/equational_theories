import equational_theories.Parastrophes.PlasticImageObstructions
import equational_theories.Parastrophes.GoldenImageObstructions

/-! Additional source laws satisfied by the same quadratic and cubic matrix
families. Each proof checks the law coordinatewise over every ZMod n, then uses
the shared Boolean-join obstruction to every single-equation characterization. -/
namespace Parastrophes.Catalogue

/-- The plastic115 matrix family obstructs E2734's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation2734_fin :
    ¬ SingleEquation .fin Law2734 .left := by
  apply PlasticImage.obstruction115
  intro n _
  apply (@Law2734.models_iff _ (PlasticImage.m115 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m115_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic222 matrix family obstructs E883's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation883_fin :
    ¬ SingleEquation .fin Law883 .left := by
  apply PlasticImage.obstruction222
  intro n _
  apply (@Law883.models_iff _ (PlasticImage.m222 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m222_op]
  ext i; fin_cases i <;> simp [PlasticImage.T, PlasticImage.Ti] <;> ring

/-- The plastic222 matrix family obstructs E1279's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation1279_fin :
    ¬ SingleEquation .fin Law1279 .left := by
  apply PlasticImage.obstruction222
  intro n _
  apply (@Law1279.models_iff _ (PlasticImage.m222 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m222_op]
  ext i; fin_cases i <;> simp [PlasticImage.T, PlasticImage.Ti] <;> ring

/-- The plastic222 matrix family obstructs E2497's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation2497_fin :
    ¬ SingleEquation .fin Law2497 .left := by
  apply PlasticImage.obstruction222
  intro n _
  apply (@Law2497.models_iff _ (PlasticImage.m222 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m222_op]
  ext i; fin_cases i <;> simp [PlasticImage.T, PlasticImage.Ti] <;> ring

/-- The plastic222 matrix family obstructs E2903's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation2903_fin :
    ¬ SingleEquation .fin Law2903 .left := by
  apply PlasticImage.obstruction222
  intro n _
  apply (@Law2903.models_iff _ (PlasticImage.m222 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m222_op]
  ext i; fin_cases i <;> simp [PlasticImage.T, PlasticImage.Ti] <;> ring

/-- The golden124 matrix family obstructs E707's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation707_fin :
    ¬ SingleEquation .fin Law707 .left := by
  apply GoldenImage.obstruction
  intro n _
  apply (@Law707.models_iff _ (GoldenImage.source (R := ZMod n))).mpr
  intro x y
  simp only [GoldenImage.source_op]
  ext i; fin_cases i <;> simp [GoldenImage.T, GoldenImage.Ti] <;> ring

/-- The golden124 matrix family obstructs E906's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation906_fin :
    ¬ SingleEquation .fin Law906 .left := by
  apply GoldenImage.obstruction
  intro n _
  apply (@Law906.models_iff _ (GoldenImage.source (R := ZMod n))).mpr
  intro x y
  simp only [GoldenImage.source_op]
  ext i; fin_cases i <;> simp [GoldenImage.T, GoldenImage.Ti] <;> ring

/-- The golden124 matrix family obstructs E1322's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation1322_fin :
    ¬ SingleEquation .fin Law1322 .left := by
  apply GoldenImage.obstruction
  intro n _
  apply (@Law1322.models_iff _ (GoldenImage.source (R := ZMod n))).mpr
  intro x y
  simp only [GoldenImage.source_op]
  ext i; fin_cases i <;> simp [GoldenImage.T, GoldenImage.Ti] <;> ring

/-- The plastic667 matrix family obstructs E667's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation667_fin :
    ¬ SingleEquation .fin Law667 .left := by
  apply PlasticImage.obstruction667
  intro n _
  apply (@Law667.models_iff _ (PlasticImage.m667 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m667_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic271 matrix family obstructs E271's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation271_fin :
    ¬ SingleEquation .fin Law271 .left := by
  apply PlasticImage.obstruction271
  intro n _
  apply (@Law271.models_iff _ (PlasticImage.m271 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m271_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic271 matrix family obstructs E2091's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation2091_fin :
    ¬ SingleEquation .fin Law2091 .left := by
  apply PlasticImage.obstruction271
  intro n _
  apply (@Law2091.models_iff _ (PlasticImage.m271 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m271_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic271 matrix family obstructs E2900's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation2900_fin :
    ¬ SingleEquation .fin Law2900 .left := by
  apply PlasticImage.obstruction271
  intro n _
  apply (@Law2900.models_iff _ (PlasticImage.m271 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m271_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic271 matrix family obstructs E3140's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation3140_fin :
    ¬ SingleEquation .fin Law3140 .left := by
  apply PlasticImage.obstruction271
  intro n _
  apply (@Law3140.models_iff _ (PlasticImage.m271 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m271_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The plastic1119 matrix family obstructs E1119's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation1119_fin :
    ¬ SingleEquation .fin Law1119 .left := by
  apply PlasticImage.obstruction1119
  intro n _
  apply (@Law1119.models_iff _ (PlasticImage.m1119 (R := ZMod n))).mpr
  intro x y
  simp only [PlasticImage.m1119_op]
  ext i; fin_cases i <;> simp [PlasticImage.T] <;> ring

/-- The golden679 matrix family obstructs E679's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation679_fin :
    ¬ SingleEquation .fin Law679 .left := by
  apply GoldenImage.obstruction679
  intro n _
  apply (@Law679.models_iff _ (GoldenImage.m679 (R := ZMod n))).mpr
  intro x y
  simp only [GoldenImage.m679_op]
  ext i; fin_cases i <;> simp [GoldenImage.T] <;> ring

end Parastrophes.Catalogue

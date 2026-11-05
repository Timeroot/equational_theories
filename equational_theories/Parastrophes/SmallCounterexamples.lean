import Mathlib.Data.Fin.VecNotation
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-! Small counterexamples for the remaining quasigroup questions. Each table and
law is checked by ordinary kernel reduction; no SAT or native-decide axioms. -/
namespace Parastrophes.Catalogue

/-- The displayed three-element E508 magma has a repeated entry in a column. -/
@[parastrophe_result] theorem not_rightQuasigroup508 : ¬ SideQuasigroupLaw .fin Law508 .right := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![1, 0, 2], ![2, 1, 0]] x y⟩
  have hm : @Equation508 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law508.models_iff _ M).mpr hm)
  have bad := (hQ 1).1 (a₁ := 0) (a₂ := 2) (by decide)
  exact (by decide : (0 : Fin 3) ≠ 2) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup508 : ¬ QuasigroupLaw .fin Law508 :=
  fun h => not_rightQuasigroup508 (quasigroup_side h .right)

/-- The displayed three-element E1489 magma has a repeated entry in a row. -/
@[parastrophe_result] theorem not_leftQuasigroup1489 : ¬ SideQuasigroupLaw .fin Law1489 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 1], ![2, 1, 2], ![0, 0, 2]] x y⟩
  have hm : @Equation1489 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1489.models_iff _ M).mpr hm)
  have bad := (hQ 0).1 (a₁ := 1) (a₂ := 2) (by decide)
  exact (by decide : (1 : Fin 3) ≠ 2) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1489 : ¬ QuasigroupLaw .fin Law1489 :=
  fun h => not_leftQuasigroup1489 (quasigroup_side h .left)

/-- The displayed three-element E1523 magma has a repeated entry in a row. -/
@[parastrophe_result] theorem not_leftQuasigroup1523 : ¬ SideQuasigroupLaw .fin Law1523 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![1, 0, 0], ![2, 0, 0]] x y⟩
  have hm : @Equation1523 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1523.models_iff _ M).mpr hm)
  have bad := (hQ 1).1 (a₁ := 1) (a₂ := 2) (by decide)
  exact (by decide : (1 : Fin 3) ≠ 2) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1523 : ¬ QuasigroupLaw .fin Law1523 :=
  fun h => not_leftQuasigroup1523 (quasigroup_side h .left)

/-- The displayed three-element E1682 magma has a repeated entry in a row. -/
@[parastrophe_result] theorem not_leftQuasigroup1682 : ¬ SideQuasigroupLaw .fin Law1682 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 0, 1], ![2, 1, 2], ![0, 2, 1]] x y⟩
  have hm : @Equation1682 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1682.models_iff _ M).mpr hm)
  have bad := (hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide)
  exact (by decide : (0 : Fin 3) ≠ 1) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1682 : ¬ QuasigroupLaw .fin Law1682 :=
  fun h => not_leftQuasigroup1682 (quasigroup_side h .left)

/-- The displayed three-element E1685 magma has a repeated entry in a row. -/
@[parastrophe_result] theorem not_leftQuasigroup1685 : ¬ SideQuasigroupLaw .fin Law1685 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![1, 0, 2], ![2, 0, 0], ![0, 2, 1]] x y⟩
  have hm : @Equation1685 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1685.models_iff _ M).mpr hm)
  have bad := (hQ 1).1 (a₁ := 1) (a₂ := 2) (by decide)
  exact (by decide : (1 : Fin 3) ≠ 2) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1685 : ¬ QuasigroupLaw .fin Law1685 :=
  fun h => not_leftQuasigroup1685 (quasigroup_side h .left)

/-- A 4-element counterexample found by table search, checked in the kernel. -/
@[parastrophe_result] theorem not_rightQuasigroup501 : ¬ SideQuasigroupLaw .fin Law501 .right := by
  intro h
  let M : Magma (Fin 4) := ⟨fun x y => ![![1, 0, 3, 2], ![2, 3, 1, 0], ![3, 0, 1, 2], ![2, 0, 3, 1]] x y⟩
  have hm : @Equation501 (Fin 4) M := by decide
  have hQ := h (Fin 4) M (inferInstance : Finite (Fin 4))
    ((@Law501.models_iff _ M).mpr hm)
  have bad := (hQ 0).1 (a₁ := 1) (a₂ := 3) (by decide)
  exact (by decide : (1 : Fin 4) ≠ 3) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup501 : ¬ QuasigroupLaw .fin Law501 :=
  fun h => not_rightQuasigroup501 (quasigroup_side h .right)

/-- A 4-element counterexample found by table search, checked in the kernel. -/
@[parastrophe_result] theorem not_rightQuasigroup670 : ¬ SideQuasigroupLaw .fin Law670 .right := by
  intro h
  let M : Magma (Fin 4) := ⟨fun x y => ![![3, 0, 1, 2], ![1, 2, 3, 0], ![1, 3, 0, 2], ![2, 0, 3, 1]] x y⟩
  have hm : @Equation670 (Fin 4) M := by decide
  have hQ := h (Fin 4) M (inferInstance : Finite (Fin 4))
    ((@Law670.models_iff _ M).mpr hm)
  have bad := (hQ 0).1 (a₁ := 1) (a₂ := 2) (by decide)
  exact (by decide : (1 : Fin 4) ≠ 2) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup670 : ¬ QuasigroupLaw .fin Law670 :=
  fun h => not_rightQuasigroup670 (quasigroup_side h .right)

/-- A 5-element counterexample found by table search, checked in the kernel. -/
@[parastrophe_result] theorem not_rightQuasigroup474 : ¬ SideQuasigroupLaw .fin Law474 .right := by
  intro h
  let M : Magma (Fin 5) := ⟨fun x y => ![![1, 0, 2, 3, 4], ![4, 1, 3, 2, 0], ![0, 2, 1, 3, 4], ![0, 3, 2, 1, 4], ![0, 4, 2, 3, 1]] x y⟩
  have hm : @Equation474 (Fin 5) M := by decide
  have hQ := h (Fin 5) M (inferInstance : Finite (Fin 5))
    ((@Law474.models_iff _ M).mpr hm)
  have bad := (hQ 0).1 (a₁ := 2) (a₂ := 3) (by decide)
  exact (by decide : (2 : Fin 5) ≠ 3) bad

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup474 : ¬ QuasigroupLaw .fin Law474 :=
  fun h => not_rightQuasigroup474 (quasigroup_side h .right)

end Parastrophes.Catalogue

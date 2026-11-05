import Mathlib.Data.Fin.VecNotation
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-! Small finite counterexamples identifying the failed translation.
The search only chooses tables; ordinary kernel reduction checks every law and collision. -/
namespace Parastrophes.Catalogue

/-- A 2-element E1697 model with a collision in row 1, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1697_small :
    ¬ SideQuasigroupLaw .fin Law1697 .left := by
  intro h
  let M : Magma (Fin 2) := ⟨fun x y => ![![1, 0], ![0, 0]] x y⟩
  have hm : @Equation1697 (Fin 2) M := by decide
  have hQ := h (Fin 2) M (inferInstance : Finite (Fin 2))
    ((@Law1697.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 2) ≠ 1) ((hQ 1).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1738 model with a collision in row 1, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1738_small :
    ¬ SideQuasigroupLaw .fin Law1738 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 2, 1], ![0, 0, 1], ![0, 2, 0]] x y⟩
  have hm : @Equation1738 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1738.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 1).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1885 model with a collision in row 0, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1885_small :
    ¬ SideQuasigroupLaw .fin Law1885 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 0, 1], ![2, 2, 1], ![0, 1, 2]] x y⟩
  have hm : @Equation1885 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1885.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1887 model with a collision in row 2, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1887_small :
    ¬ SideQuasigroupLaw .fin Law1887 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 2, 1], ![0, 2, 1], ![2, 2, 0]] x y⟩
  have hm : @Equation1887 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1887.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 2).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1897 model with a collision in row 0, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1897_small :
    ¬ SideQuasigroupLaw .fin Law1897 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 0, 2], ![2, 1, 0], ![1, 1, 0]] x y⟩
  have hm : @Equation1897 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1897.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1922 model with a collision in row 0, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1922_small :
    ¬ SideQuasigroupLaw .fin Law1922 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![1, 1, 2], ![2, 0, 1], ![1, 2, 0]] x y⟩
  have hm : @Equation1922 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1922.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E1975 model with a collision in row 1, columns 0 and 2. -/
@[parastrophe_result] theorem not_leftQuasigroup1975_small :
    ¬ SideQuasigroupLaw .fin Law1975 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 2, 1], ![0, 2, 0], ![0, 0, 1]] x y⟩
  have hm : @Equation1975 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law1975.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 2) ((hQ 1).1 (a₁ := 0) (a₂ := 2) (by decide))

/-- A 3-element E2093 model with a collision in row 0, columns 0 and 2. -/
@[parastrophe_result] theorem not_leftQuasigroup2093_small :
    ¬ SideQuasigroupLaw .fin Law2093 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![1, 0, 1], ![2, 2, 1], ![2, 0, 0]] x y⟩
  have hm : @Equation2093 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2093.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 2) ((hQ 0).1 (a₁ := 0) (a₂ := 2) (by decide))

/-- A 3-element E2097 model with a collision in row 0, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2097_small :
    ¬ SideQuasigroupLaw .fin Law2097 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 0, 1], ![2, 2, 1], ![2, 0, 0]] x y⟩
  have hm : @Equation2097 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2097.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E2098 model with a collision in row 0, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2098_small :
    ¬ SideQuasigroupLaw .fin Law2098 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 0, 1], ![2, 1, 1], ![2, 0, 2]] x y⟩
  have hm : @Equation2098 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2098.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 2-element E2420 model with a collision in row 1, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2420_small :
    ¬ SideQuasigroupLaw .fin Law2420 .left := by
  intro h
  let M : Magma (Fin 2) := ⟨fun x y => ![![0, 1], ![0, 0]] x y⟩
  have hm : @Equation2420 (Fin 2) M := by decide
  have hQ := h (Fin 2) M (inferInstance : Finite (Fin 2))
    ((@Law2420.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 2) ≠ 1) ((hQ 1).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E2499 model with a collision in row 0, columns 1 and 2. -/
@[parastrophe_result] theorem not_leftQuasigroup2499_small :
    ¬ SideQuasigroupLaw .fin Law2499 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 1], ![0, 1, 2], ![1, 1, 2]] x y⟩
  have hm : @Equation2499 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2499.models_iff _ M).mpr hm)
  exact (by decide : (1 : Fin 3) ≠ 2) ((hQ 0).1 (a₁ := 1) (a₂ := 2) (by decide))

/-- A 2-element E2536 model with a collision in row 1, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2536_small :
    ¬ SideQuasigroupLaw .fin Law2536 .left := by
  intro h
  let M : Magma (Fin 2) := ⟨fun x y => ![![0, 1], ![0, 0]] x y⟩
  have hm : @Equation2536 (Fin 2) M := by decide
  have hQ := h (Fin 2) M (inferInstance : Finite (Fin 2))
    ((@Law2536.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 2) ≠ 1) ((hQ 1).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E2592 model with a collision in row 2, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2592_small :
    ¬ SideQuasigroupLaw .fin Law2592 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![0, 1, 2], ![2, 2, 0]] x y⟩
  have hm : @Equation2592 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2592.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 2).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E2609 model with a collision in row 1, columns 0 and 2. -/
@[parastrophe_result] theorem not_leftQuasigroup2609_small :
    ¬ SideQuasigroupLaw .fin Law2609 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![0, 2, 0], ![0, 0, 1]] x y⟩
  have hm : @Equation2609 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2609.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 2) ((hQ 1).1 (a₁ := 0) (a₂ := 2) (by decide))

/-- A 3-element E2808 model with a collision in row 2, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2808_small :
    ¬ SideQuasigroupLaw .fin Law2808 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![0, 1, 2], ![2, 2, 0]] x y⟩
  have hm : @Equation2808 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2808.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 2).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 3-element E2964 model with a collision in row 2, columns 0 and 2. -/
@[parastrophe_result] theorem not_leftQuasigroup2964_small :
    ¬ SideQuasigroupLaw .fin Law2964 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![0, 1, 2], ![1, 2, 1]] x y⟩
  have hm : @Equation2964 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2964.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 2) ((hQ 2).1 (a₁ := 0) (a₂ := 2) (by decide))

/-- A 3-element E2998 model with a collision in row 2, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup2998_small :
    ¬ SideQuasigroupLaw .fin Law2998 .left := by
  intro h
  let M : Magma (Fin 3) := ⟨fun x y => ![![0, 1, 2], ![0, 1, 2], ![2, 2, 0]] x y⟩
  have hm : @Equation2998 (Fin 3) M := by decide
  have hQ := h (Fin 3) M (inferInstance : Finite (Fin 3))
    ((@Law2998.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 3) ≠ 1) ((hQ 2).1 (a₁ := 0) (a₂ := 1) (by decide))


/-- A 4-element E273 model with a collision in row 3, columns 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup273_small :
    ¬ SideQuasigroupLaw .fin Law273 .left := by
  intro h
  let M : Magma (Fin 4) := ⟨fun x y => ![![3, 1, 2, 0], ![0, 3, 2, 1], ![0, 1, 3, 2], ![2, 2, 0, 3]] x y⟩
  have hm : @Equation273 (Fin 4) M := by decide
  have hQ := h (Fin 4) M (inferInstance : Finite (Fin 4))
    ((@Law273.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 4) ≠ 1) ((hQ 3).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- A 4-element E1488 model with a collision in row 2, columns 2 and 3. -/
@[parastrophe_result] theorem not_leftQuasigroup1488_small :
    ¬ SideQuasigroupLaw .fin Law1488 .left := by
  intro h
  let M : Magma (Fin 4) := ⟨fun x y => ![![0, 3, 2, 1], ![0, 1, 2, 3], ![2, 1, 0, 0], ![0, 3, 2, 1]] x y⟩
  have hm : @Equation1488 (Fin 4) M := by decide
  have hQ := h (Fin 4) M (inferInstance : Finite (Fin 4))
    ((@Law1488.models_iff _ M).mpr hm)
  exact (by decide : (2 : Fin 4) ≠ 3) ((hQ 2).1 (a₁ := 2) (a₂ := 3) (by decide))

/-- A 4-element E2912 model with a collision in row 0, columns 0 and 3. -/
@[parastrophe_result] theorem not_leftQuasigroup2912_small :
    ¬ SideQuasigroupLaw .fin Law2912 .left := by
  intro h
  let M : Magma (Fin 4) := ⟨fun x y => ![![0, 1, 2, 0], ![2, 3, 3, 2], ![0, 0, 2, 3], ![1, 2, 0, 0]] x y⟩
  have hm : @Equation2912 (Fin 4) M := by decide
  have hQ := h (Fin 4) M (inferInstance : Finite (Fin 4))
    ((@Law2912.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 4) ≠ 3) ((hQ 0).1 (a₁ := 0) (a₂ := 3) (by decide))

/-- A 5-element E2939 model with a collision in row 2, columns 1 and 3. -/
@[parastrophe_result] theorem not_leftQuasigroup2939_small :
    ¬ SideQuasigroupLaw .fin Law2939 .left := by
  intro h
  let M : Magma (Fin 5) := ⟨fun x y => ![![0, 2, 3, 1, 4], ![2, 0, 1, 3, 4], ![1, 4, 2, 4, 0], ![4, 1, 0, 3, 2], ![0, 1, 4, 2, 3]] x y⟩
  have hm : @Equation2939 (Fin 5) M := by decide
  have hQ := h (Fin 5) M (inferInstance : Finite (Fin 5))
    ((@Law2939.models_iff _ M).mpr hm)
  exact (by decide : (1 : Fin 5) ≠ 3) ((hQ 2).1 (a₁ := 1) (a₂ := 3) (by decide))

/-- A 6-element E2994 model with a collision in row 1, columns 0 and 5. -/
@[parastrophe_result] theorem not_leftQuasigroup2994_small :
    ¬ SideQuasigroupLaw .fin Law2994 .left := by
  intro h
  let M : Magma (Fin 6) := ⟨fun x y => ![![0, 1, 2, 3, 4, 5], ![0, 4, 4, 2, 4, 0], ![0, 1, 2, 3, 4, 5], ![0, 1, 4, 1, 0, 0], ![3, 2, 0, 2, 5, 5], ![1, 2, 4, 1, 0, 3]] x y⟩
  have hm : @Equation2994 (Fin 6) M := by decide
  have hQ := h (Fin 6) M (inferInstance : Finite (Fin 6))
    ((@Law2994.models_iff _ M).mpr hm)
  exact (by decide : (0 : Fin 6) ≠ 5) ((hQ 1).1 (a₁ := 0) (a₂ := 5) (by decide))

end Parastrophes.Catalogue

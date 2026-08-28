import equational_theories.Definability.Srch_S8R58

/-!
# Structural certificate targets: `Magma.srch8R58`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R58_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 636 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R58_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 836 takes them (67 nodes). -/
def ordS8R58_Law836 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 836. -/
theorem noS8R58_Law836 : ∀ v : Magma.tup8R58,
    ¬ @Equation836 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (184 nodes). -/
def ordS8R58_Law1036 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1036. -/
theorem noS8R58_Law1036 : ∀ v : Magma.tup8R58,
    ¬ @Equation1036 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (67 nodes). -/
def ordS8R58_Law1249 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1249. -/
theorem noS8R58_Law1249 : ∀ v : Magma.tup8R58,
    ¬ @Equation1249 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (67 nodes). -/
def ordS8R58_Law2303 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2303. -/
theorem noS8R58_Law2303 : ∀ v : Magma.tup8R58,
    ¬ @Equation2303 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (184 nodes). -/
def ordS8R58_Law2496 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2496. -/
theorem noS8R58_Law2496 : ∀ v : Magma.tup8R58,
    ¬ @Equation2496 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (67 nodes). -/
def ordS8R58_Law2736 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2736. -/
theorem noS8R58_Law2736 : ∀ v : Magma.tup8R58,
    ¬ @Equation2736 (Fin 8) (Magma.srch8R58 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S8R58.E) (tr := S8R58.tr) (z := S8R58.z)
    (st := S8R58.st) (X := S8R58.X) (envs := Magma.envsRed 8 S8R58.E 2)
    (ord := ordS8R58_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 8) (Magma.srch8R58 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R58_refutes_0 :
    FamilyRefutes Magma.srch8R58 [
      836, 1036, 1249, 2303, 2496, 2736
    ] :=
  ⟨noS8R58_Law836, noS8R58_Law1036, noS8R58_Law1249, noS8R58_Law2303, noS8R58_Law2496, noS8R58_Law2736⟩

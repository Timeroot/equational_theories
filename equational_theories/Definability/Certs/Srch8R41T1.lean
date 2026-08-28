import equational_theories.Definability.Srch_S8R41

/-!
# Structural certificate targets: `Magma.srch8R41` (part 2 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R41_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,753 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R41_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3324 takes them (605 nodes). -/
def ordS8R41_Law3324 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3324. -/
theorem noS8R41_Law3324 : ∀ v : Magma.tup8R41,
    ¬ @Equation3324 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 4)
    (ord := ordS8R41_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3388 takes them (859 nodes). -/
def ordS8R41_Law3388 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3388. -/
theorem noS8R41_Law3388 : ∀ v : Magma.tup8R41,
    ¬ @Equation3388 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3388) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3388) (by native_decide) v.1 v.2
    ((@Law3388.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (890 nodes). -/
def ordS8R41_Law3523 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3523. -/
theorem noS8R41_Law3523 : ∀ v : Magma.tup8R41,
    ¬ @Equation3523 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (748 nodes). -/
def ordS8R41_Law3524 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3524. -/
theorem noS8R41_Law3524 : ∀ v : Magma.tup8R41,
    ¬ @Equation3524 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (651 nodes). -/
def ordS8R41_Law3527 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3527. -/
theorem noS8R41_Law3527 : ∀ v : Magma.tup8R41,
    ¬ @Equation3527 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 4)
    (ord := ordS8R41_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R41_refutes_1 :
    FamilyRefutes Magma.srch8R41 [
      3324, 3388, 3523, 3524, 3527
    ] :=
  ⟨noS8R41_Law3324, noS8R41_Law3388, noS8R41_Law3523, noS8R41_Law3524, noS8R41_Law3527⟩

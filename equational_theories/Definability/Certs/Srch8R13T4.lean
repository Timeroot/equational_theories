import equational_theories.Definability.Srch_S8R13

/-!
# Structural certificate targets: `Magma.srch8R13` (part 5 of 85)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 2,760 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 318 takes them (461 nodes). -/
def ordS8R13_Law318 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 318. -/
theorem noS8R13_Law318 : ∀ v : Magma.tup8R13,
    ¬ @Equation318 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law318) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law318) (by native_decide) v.1 v.2
    ((@Law318.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 336 takes them (871 nodes). -/
def ordS8R13_Law336 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 336. -/
theorem noS8R13_Law336 : ∀ v : Magma.tup8R13,
    ¬ @Equation336 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law336) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 2)
    (ord := ordS8R13_Law336) (by native_decide) v.1 v.2
    ((@Law336.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 339 takes them (440 nodes). -/
def ordS8R13_Law339 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 339. -/
theorem noS8R13_Law339 : ∀ v : Magma.tup8R13,
    ¬ @Equation339 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law339) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law339) (by native_decide) v.1 v.2
    ((@Law339.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 347 takes them (465 nodes). -/
def ordS8R13_Law347 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 347. -/
theorem noS8R13_Law347 : ∀ v : Magma.tup8R13,
    ¬ @Equation347 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law347) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law347) (by native_decide) v.1 v.2
    ((@Law347.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 351 takes them (63 nodes). -/
def ordS8R13_Law351 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 351. -/
theorem noS8R13_Law351 : ∀ v : Magma.tup8R13,
    ¬ @Equation351 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law351) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law351) (by native_decide) v.1 v.2
    ((@Law351.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 355 takes them (59 nodes). -/
def ordS8R13_Law355 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 355. -/
theorem noS8R13_Law355 : ∀ v : Magma.tup8R13,
    ¬ @Equation355 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law355) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law355) (by native_decide) v.1 v.2
    ((@Law355.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 363 takes them (401 nodes). -/
def ordS8R13_Law363 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 363. -/
theorem noS8R13_Law363 : ∀ v : Magma.tup8R13,
    ¬ @Equation363 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law363) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law363) (by native_decide) v.1 v.2
    ((@Law363.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R13_refutes_4 :
    FamilyRefutes Magma.srch8R13 [
      318, 336, 339, 347, 351, 355, 363
    ] :=
  ⟨noS8R13_Law318, noS8R13_Law336, noS8R13_Law339, noS8R13_Law347, noS8R13_Law351, noS8R13_Law355, noS8R13_Law363⟩

import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 6 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `15`
equations here, 3,350 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 324 takes them (769 nodes). -/
def ordS8R9_Law324 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 324. -/
theorem noS8R9_Law324 : ∀ v : Magma.tup8R9,
    ¬ @Equation324 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law324) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law324) (by native_decide) v.1 v.2
    ((@Law324.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 328 takes them (776 nodes). -/
def ordS8R9_Law328 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 328. -/
theorem noS8R9_Law328 : ∀ v : Magma.tup8R9,
    ¬ @Equation328 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law328) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law328) (by native_decide) v.1 v.2
    ((@Law328.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 330 takes them (65 nodes). -/
def ordS8R9_Law330 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 330. -/
theorem noS8R9_Law330 : ∀ v : Magma.tup8R9,
    ¬ @Equation330 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law330) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law330) (by native_decide) v.1 v.2
    ((@Law330.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 331 takes them (65 nodes). -/
def ordS8R9_Law331 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 331. -/
theorem noS8R9_Law331 : ∀ v : Magma.tup8R9,
    ¬ @Equation331 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law331) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law331) (by native_decide) v.1 v.2
    ((@Law331.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 339 takes them (741 nodes). -/
def ordS8R9_Law339 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 339. -/
theorem noS8R9_Law339 : ∀ v : Magma.tup8R9,
    ¬ @Equation339 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law339) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law339) (by native_decide) v.1 v.2
    ((@Law339.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 343 takes them (9 nodes). -/
def ordS8R9_Law343 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 343. -/
theorem noS8R9_Law343 : ∀ v : Magma.tup8R9,
    ¬ @Equation343 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law343) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law343) (by native_decide) v.1 v.2
    ((@Law343.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 347 takes them (9 nodes). -/
def ordS8R9_Law347 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 347. -/
theorem noS8R9_Law347 : ∀ v : Magma.tup8R9,
    ¬ @Equation347 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law347) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law347) (by native_decide) v.1 v.2
    ((@Law347.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 351 takes them (741 nodes). -/
def ordS8R9_Law351 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 351. -/
theorem noS8R9_Law351 : ∀ v : Magma.tup8R9,
    ¬ @Equation351 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law351) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law351) (by native_decide) v.1 v.2
    ((@Law351.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 355 takes them (9 nodes). -/
def ordS8R9_Law355 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 355. -/
theorem noS8R9_Law355 : ∀ v : Magma.tup8R9,
    ¬ @Equation355 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law355) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law355) (by native_decide) v.1 v.2
    ((@Law355.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 360 takes them (9 nodes). -/
def ordS8R9_Law360 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 360. -/
theorem noS8R9_Law360 : ∀ v : Magma.tup8R9,
    ¬ @Equation360 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law360) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law360) (by native_decide) v.1 v.2
    ((@Law360.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 363 takes them (9 nodes). -/
def ordS8R9_Law363 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 363. -/
theorem noS8R9_Law363 : ∀ v : Magma.tup8R9,
    ¬ @Equation363 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law363) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law363) (by native_decide) v.1 v.2
    ((@Law363.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 367 takes them (65 nodes). -/
def ordS8R9_Law367 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 367. -/
theorem noS8R9_Law367 : ∀ v : Magma.tup8R9,
    ¬ @Equation367 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law367) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law367) (by native_decide) v.1 v.2
    ((@Law367.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 370 takes them (65 nodes). -/
def ordS8R9_Law370 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 370. -/
theorem noS8R9_Law370 : ∀ v : Magma.tup8R9,
    ¬ @Equation370 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law370) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law370) (by native_decide) v.1 v.2
    ((@Law370.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 376 takes them (9 nodes). -/
def ordS8R9_Law376 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 376. -/
theorem noS8R9_Law376 : ∀ v : Magma.tup8R9,
    ¬ @Equation376 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law376) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law376) (by native_decide) v.1 v.2
    ((@Law376.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 379 takes them (9 nodes). -/
def ordS8R9_Law379 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 379. -/
theorem noS8R9_Law379 : ∀ v : Magma.tup8R9,
    ¬ @Equation379 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law379) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law379) (by native_decide) v.1 v.2
    ((@Law379.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srch8R9_refutes_5 :
    FamilyRefutes Magma.srch8R9 [
      324, 328, 330, 331, 339, 343, 347, 351, 355, 360, 363, 367, 370, 376, 379
    ] :=
  ⟨noS8R9_Law324, noS8R9_Law328, noS8R9_Law330, noS8R9_Law331, noS8R9_Law339, noS8R9_Law343, noS8R9_Law347, noS8R9_Law351, noS8R9_Law355, noS8R9_Law360, noS8R9_Law363, noS8R9_Law367, noS8R9_Law370, noS8R9_Law376, noS8R9_Law379⟩

import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 7 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 3,355 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1227 takes them (168 nodes). -/
def ordS8R52_Law1227 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1227. -/
theorem noS8R52_Law1227 : ∀ v : Magma.tup8R52,
    ¬ @Equation1227 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1227) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1227) (by native_decide) v.1 v.2
    ((@Law1227.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1230 takes them (156 nodes). -/
def ordS8R52_Law1230 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1230. -/
theorem noS8R52_Law1230 : ∀ v : Magma.tup8R52,
    ¬ @Equation1230 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1230) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1230) (by native_decide) v.1 v.2
    ((@Law1230.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1232 takes them (308 nodes). -/
def ordS8R52_Law1232 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1232. -/
theorem noS8R52_Law1232 : ∀ v : Magma.tup8R52,
    ¬ @Equation1232 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1232) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1232) (by native_decide) v.1 v.2
    ((@Law1232.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1233 takes them (144 nodes). -/
def ordS8R52_Law1233 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1233. -/
theorem noS8R52_Law1233 : ∀ v : Magma.tup8R52,
    ¬ @Equation1233 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1233) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1233) (by native_decide) v.1 v.2
    ((@Law1233.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1235 takes them (152 nodes). -/
def ordS8R52_Law1235 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1235. -/
theorem noS8R52_Law1235 : ∀ v : Magma.tup8R52,
    ¬ @Equation1235 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1235) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1235) (by native_decide) v.1 v.2
    ((@Law1235.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1236 takes them (152 nodes). -/
def ordS8R52_Law1236 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1236. -/
theorem noS8R52_Law1236 : ∀ v : Magma.tup8R52,
    ¬ @Equation1236 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1236) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1236) (by native_decide) v.1 v.2
    ((@Law1236.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1237 takes them (144 nodes). -/
def ordS8R52_Law1237 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1237. -/
theorem noS8R52_Law1237 : ∀ v : Magma.tup8R52,
    ¬ @Equation1237 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1237) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law1237) (by native_decide) v.1 v.2
    ((@Law1237.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1288 takes them (477 nodes). -/
def ordS8R52_Law1288 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1288. -/
theorem noS8R52_Law1288 : ∀ v : Magma.tup8R52,
    ¬ @Equation1288 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1288) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1288) (by native_decide) v.1 v.2
    ((@Law1288.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1299 takes them (217 nodes). -/
def ordS8R52_Law1299 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1299. -/
theorem noS8R52_Law1299 : ∀ v : Magma.tup8R52,
    ¬ @Equation1299 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1299) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1299) (by native_decide) v.1 v.2
    ((@Law1299.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (577 nodes). -/
def ordS8R52_Law1325 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1325. -/
theorem noS8R52_Law1325 : ∀ v : Magma.tup8R52,
    ¬ @Equation1325 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1336 takes them (217 nodes). -/
def ordS8R52_Law1336 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1336. -/
theorem noS8R52_Law1336 : ∀ v : Magma.tup8R52,
    ¬ @Equation1336 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1336) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1336) (by native_decide) v.1 v.2
    ((@Law1336.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1370 takes them (225 nodes). -/
def ordS8R52_Law1370 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1370. -/
theorem noS8R52_Law1370 : ∀ v : Magma.tup8R52,
    ¬ @Equation1370 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1370) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1370) (by native_decide) v.1 v.2
    ((@Law1370.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1387 takes them (225 nodes). -/
def ordS8R52_Law1387 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1387. -/
theorem noS8R52_Law1387 : ∀ v : Magma.tup8R52,
    ¬ @Equation1387 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1387) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1387) (by native_decide) v.1 v.2
    ((@Law1387.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1405 takes them (193 nodes). -/
def ordS8R52_Law1405 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1405. -/
theorem noS8R52_Law1405 : ∀ v : Magma.tup8R52,
    ¬ @Equation1405 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1405) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law1405) (by native_decide) v.1 v.2
    ((@Law1405.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch8R52_refutes_6 :
    FamilyRefutes Magma.srch8R52 [
      1227, 1230, 1232, 1233, 1235, 1236, 1237, 1288, 1299, 1325, 1336, 1370, 1387, 1405
    ] :=
  ⟨noS8R52_Law1227, noS8R52_Law1230, noS8R52_Law1232, noS8R52_Law1233, noS8R52_Law1235, noS8R52_Law1236, noS8R52_Law1237, noS8R52_Law1288, noS8R52_Law1299, noS8R52_Law1325, noS8R52_Law1336, noS8R52_Law1370, noS8R52_Law1387, noS8R52_Law1405⟩

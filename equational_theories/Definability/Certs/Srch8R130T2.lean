import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 3 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 296 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1252 takes them (3 nodes). -/
def ordS8R130_Law1252 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1252. -/
theorem noS8R130_Law1252 : ∀ v : Magma.tup8R130,
    ¬ @Equation1252 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1252) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1252) (by native_decide) v.1 v.2
    ((@Law1252.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1253 takes them (3 nodes). -/
def ordS8R130_Law1253 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1253. -/
theorem noS8R130_Law1253 : ∀ v : Magma.tup8R130,
    ¬ @Equation1253 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1253) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1253) (by native_decide) v.1 v.2
    ((@Law1253.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1254 takes them (4 nodes). -/
def ordS8R130_Law1254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1254. -/
theorem noS8R130_Law1254 : ∀ v : Magma.tup8R130,
    ¬ @Equation1254 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1254) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1254) (by native_decide) v.1 v.2
    ((@Law1254.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1255 takes them (3 nodes). -/
def ordS8R130_Law1255 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1255. -/
theorem noS8R130_Law1255 : ∀ v : Magma.tup8R130,
    ¬ @Equation1255 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1255) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1255) (by native_decide) v.1 v.2
    ((@Law1255.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1256 takes them (3 nodes). -/
def ordS8R130_Law1256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1256. -/
theorem noS8R130_Law1256 : ∀ v : Magma.tup8R130,
    ¬ @Equation1256 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1256) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1256) (by native_decide) v.1 v.2
    ((@Law1256.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1257 takes them (3 nodes). -/
def ordS8R130_Law1257 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1257. -/
theorem noS8R130_Law1257 : ∀ v : Magma.tup8R130,
    ¬ @Equation1257 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1257) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law1257) (by native_decide) v.1 v.2
    ((@Law1257.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1258 takes them (4 nodes). -/
def ordS8R130_Law1258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1258. -/
theorem noS8R130_Law1258 : ∀ v : Magma.tup8R130,
    ¬ @Equation1258 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1258) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1258) (by native_decide) v.1 v.2
    ((@Law1258.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1264 takes them (3 nodes). -/
def ordS8R130_Law1264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1264. -/
theorem noS8R130_Law1264 : ∀ v : Magma.tup8R130,
    ¬ @Equation1264 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1264) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1264) (by native_decide) v.1 v.2
    ((@Law1264.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1267 takes them (3 nodes). -/
def ordS8R130_Law1267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1267. -/
theorem noS8R130_Law1267 : ∀ v : Magma.tup8R130,
    ¬ @Equation1267 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1267) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1267) (by native_decide) v.1 v.2
    ((@Law1267.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (3 nodes). -/
def ordS8R130_Law1278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1278. -/
theorem noS8R130_Law1278 : ∀ v : Magma.tup8R130,
    ¬ @Equation1278 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (3 nodes). -/
def ordS8R130_Law1325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1325. -/
theorem noS8R130_Law1325 : ∀ v : Magma.tup8R130,
    ¬ @Equation1325 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1340 takes them (3 nodes). -/
def ordS8R130_Law1340 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1340. -/
theorem noS8R130_Law1340 : ∀ v : Magma.tup8R130,
    ¬ @Equation1340 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1340) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1340) (by native_decide) v.1 v.2
    ((@Law1340.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (3 nodes). -/
def ordS8R130_Law1374 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1374. -/
theorem noS8R130_Law1374 : ∀ v : Magma.tup8R130,
    ¬ @Equation1374 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1387 takes them (3 nodes). -/
def ordS8R130_Law1387 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1387. -/
theorem noS8R130_Law1387 : ∀ v : Magma.tup8R130,
    ¬ @Equation1387 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1387) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1387) (by native_decide) v.1 v.2
    ((@Law1387.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1427 takes them (3 nodes). -/
def ordS8R130_Law1427 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1427. -/
theorem noS8R130_Law1427 : ∀ v : Magma.tup8R130,
    ¬ @Equation1427 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1427) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1427) (by native_decide) v.1 v.2
    ((@Law1427.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1428 takes them (4 nodes). -/
def ordS8R130_Law1428 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1428. -/
theorem noS8R130_Law1428 : ∀ v : Magma.tup8R130,
    ¬ @Equation1428 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1428) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1428) (by native_decide) v.1 v.2
    ((@Law1428.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1429 takes them (3 nodes). -/
def ordS8R130_Law1429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1429. -/
theorem noS8R130_Law1429 : ∀ v : Magma.tup8R130,
    ¬ @Equation1429 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1429) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1429) (by native_decide) v.1 v.2
    ((@Law1429.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1430 takes them (3 nodes). -/
def ordS8R130_Law1430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1430. -/
theorem noS8R130_Law1430 : ∀ v : Magma.tup8R130,
    ¬ @Equation1430 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1430) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1430) (by native_decide) v.1 v.2
    ((@Law1430.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1432 takes them (3 nodes). -/
def ordS8R130_Law1432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1432. -/
theorem noS8R130_Law1432 : ∀ v : Magma.tup8R130,
    ¬ @Equation1432 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1432) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1432) (by native_decide) v.1 v.2
    ((@Law1432.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1434 takes them (4 nodes). -/
def ordS8R130_Law1434 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1434. -/
theorem noS8R130_Law1434 : ∀ v : Magma.tup8R130,
    ¬ @Equation1434 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1434) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1434) (by native_decide) v.1 v.2
    ((@Law1434.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (3 nodes). -/
def ordS8R130_Law1442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1442. -/
theorem noS8R130_Law1442 : ∀ v : Magma.tup8R130,
    ¬ @Equation1442 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (4 nodes). -/
def ordS8R130_Law1444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1444. -/
theorem noS8R130_Law1444 : ∀ v : Magma.tup8R130,
    ¬ @Equation1444 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1454 takes them (4 nodes). -/
def ordS8R130_Law1454 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1454. -/
theorem noS8R130_Law1454 : ∀ v : Magma.tup8R130,
    ¬ @Equation1454 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1454) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1454) (by native_decide) v.1 v.2
    ((@Law1454.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (3 nodes). -/
def ordS8R130_Law1455 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1455. -/
theorem noS8R130_Law1455 : ∀ v : Magma.tup8R130,
    ¬ @Equation1455 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1459 takes them (3 nodes). -/
def ordS8R130_Law1459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1459. -/
theorem noS8R130_Law1459 : ∀ v : Magma.tup8R130,
    ¬ @Equation1459 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1459) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1459) (by native_decide) v.1 v.2
    ((@Law1459.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (3 nodes). -/
def ordS8R130_Law1467 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1467. -/
theorem noS8R130_Law1467 : ∀ v : Magma.tup8R130,
    ¬ @Equation1467 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1470 takes them (3 nodes). -/
def ordS8R130_Law1470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1470. -/
theorem noS8R130_Law1470 : ∀ v : Magma.tup8R130,
    ¬ @Equation1470 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1470) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1470) (by native_decide) v.1 v.2
    ((@Law1470.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1478 takes them (3 nodes). -/
def ordS8R130_Law1478 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1478. -/
theorem noS8R130_Law1478 : ∀ v : Magma.tup8R130,
    ¬ @Equation1478 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1478) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1478) (by native_decide) v.1 v.2
    ((@Law1478.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (3 nodes). -/
def ordS8R130_Law1481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1481. -/
theorem noS8R130_Law1481 : ∀ v : Magma.tup8R130,
    ¬ @Equation1481 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1488 takes them (3 nodes). -/
def ordS8R130_Law1488 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1488. -/
theorem noS8R130_Law1488 : ∀ v : Magma.tup8R130,
    ¬ @Equation1488 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1488) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1488) (by native_decide) v.1 v.2
    ((@Law1488.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1515 takes them (3 nodes). -/
def ordS8R130_Law1515 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1515. -/
theorem noS8R130_Law1515 : ∀ v : Magma.tup8R130,
    ¬ @Equation1515 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1515) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1515) (by native_decide) v.1 v.2
    ((@Law1515.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1525 takes them (3 nodes). -/
def ordS8R130_Law1525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1525. -/
theorem noS8R130_Law1525 : ∀ v : Magma.tup8R130,
    ¬ @Equation1525 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1525) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1525) (by native_decide) v.1 v.2
    ((@Law1525.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (3 nodes). -/
def ordS8R130_Law1528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1528. -/
theorem noS8R130_Law1528 : ∀ v : Magma.tup8R130,
    ¬ @Equation1528 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1543 takes them (3 nodes). -/
def ordS8R130_Law1543 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1543. -/
theorem noS8R130_Law1543 : ∀ v : Magma.tup8R130,
    ¬ @Equation1543 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1543) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1543) (by native_decide) v.1 v.2
    ((@Law1543.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1577 takes them (3 nodes). -/
def ordS8R130_Law1577 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1577. -/
theorem noS8R130_Law1577 : ∀ v : Magma.tup8R130,
    ¬ @Equation1577 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1577) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1577) (by native_decide) v.1 v.2
    ((@Law1577.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1590 takes them (3 nodes). -/
def ordS8R130_Law1590 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1590. -/
theorem noS8R130_Law1590 : ∀ v : Magma.tup8R130,
    ¬ @Equation1590 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1590) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1590) (by native_decide) v.1 v.2
    ((@Law1590.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1630 takes them (3 nodes). -/
def ordS8R130_Law1630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1630. -/
theorem noS8R130_Law1630 : ∀ v : Magma.tup8R130,
    ¬ @Equation1630 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1630) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1630) (by native_decide) v.1 v.2
    ((@Law1630.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1631 takes them (4 nodes). -/
def ordS8R130_Law1631 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1631. -/
theorem noS8R130_Law1631 : ∀ v : Magma.tup8R130,
    ¬ @Equation1631 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1631) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1631) (by native_decide) v.1 v.2
    ((@Law1631.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (3 nodes). -/
def ordS8R130_Law1632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1632. -/
theorem noS8R130_Law1632 : ∀ v : Magma.tup8R130,
    ¬ @Equation1632 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1634 takes them (4 nodes). -/
def ordS8R130_Law1634 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1634. -/
theorem noS8R130_Law1634 : ∀ v : Magma.tup8R130,
    ¬ @Equation1634 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1634) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1634) (by native_decide) v.1 v.2
    ((@Law1634.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (3 nodes). -/
def ordS8R130_Law1635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1635. -/
theorem noS8R130_Law1635 : ∀ v : Magma.tup8R130,
    ¬ @Equation1635 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1637 takes them (4 nodes). -/
def ordS8R130_Law1637 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1637. -/
theorem noS8R130_Law1637 : ∀ v : Magma.tup8R130,
    ¬ @Equation1637 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1637) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1637) (by native_decide) v.1 v.2
    ((@Law1637.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1645 takes them (3 nodes). -/
def ordS8R130_Law1645 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1645. -/
theorem noS8R130_Law1645 : ∀ v : Magma.tup8R130,
    ¬ @Equation1645 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1645) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1645) (by native_decide) v.1 v.2
    ((@Law1645.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1647 takes them (4 nodes). -/
def ordS8R130_Law1647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1647. -/
theorem noS8R130_Law1647 : ∀ v : Magma.tup8R130,
    ¬ @Equation1647 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1647) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1647) (by native_decide) v.1 v.2
    ((@Law1647.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (4 nodes). -/
def ordS8R130_Law1654 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1654. -/
theorem noS8R130_Law1654 : ∀ v : Magma.tup8R130,
    ¬ @Equation1654 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (3 nodes). -/
def ordS8R130_Law1658 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1658. -/
theorem noS8R130_Law1658 : ∀ v : Magma.tup8R130,
    ¬ @Equation1658 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (3 nodes). -/
def ordS8R130_Law1662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1662. -/
theorem noS8R130_Law1662 : ∀ v : Magma.tup8R130,
    ¬ @Equation1662 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1670 takes them (3 nodes). -/
def ordS8R130_Law1670 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1670. -/
theorem noS8R130_Law1670 : ∀ v : Magma.tup8R130,
    ¬ @Equation1670 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1670) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1670) (by native_decide) v.1 v.2
    ((@Law1670.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1673 takes them (3 nodes). -/
def ordS8R130_Law1673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1673. -/
theorem noS8R130_Law1673 : ∀ v : Magma.tup8R130,
    ¬ @Equation1673 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1673) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1673) (by native_decide) v.1 v.2
    ((@Law1673.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1681 takes them (3 nodes). -/
def ordS8R130_Law1681 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1681. -/
theorem noS8R130_Law1681 : ∀ v : Magma.tup8R130,
    ¬ @Equation1681 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1681) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1681) (by native_decide) v.1 v.2
    ((@Law1681.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (3 nodes). -/
def ordS8R130_Law1684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1684. -/
theorem noS8R130_Law1684 : ∀ v : Magma.tup8R130,
    ¬ @Equation1684 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (3 nodes). -/
def ordS8R130_Law1691 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1691. -/
theorem noS8R130_Law1691 : ∀ v : Magma.tup8R130,
    ¬ @Equation1691 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1701 takes them (3 nodes). -/
def ordS8R130_Law1701 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1701. -/
theorem noS8R130_Law1701 : ∀ v : Magma.tup8R130,
    ¬ @Equation1701 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1701) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1701) (by native_decide) v.1 v.2
    ((@Law1701.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1718 takes them (3 nodes). -/
def ordS8R130_Law1718 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1718. -/
theorem noS8R130_Law1718 : ∀ v : Magma.tup8R130,
    ¬ @Equation1718 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1718) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1718) (by native_decide) v.1 v.2
    ((@Law1718.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (3 nodes). -/
def ordS8R130_Law1731 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1731. -/
theorem noS8R130_Law1731 : ∀ v : Magma.tup8R130,
    ¬ @Equation1731 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1746 takes them (3 nodes). -/
def ordS8R130_Law1746 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1746. -/
theorem noS8R130_Law1746 : ∀ v : Magma.tup8R130,
    ¬ @Equation1746 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1746) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1746) (by native_decide) v.1 v.2
    ((@Law1746.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (3 nodes). -/
def ordS8R130_Law1780 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1780. -/
theorem noS8R130_Law1780 : ∀ v : Magma.tup8R130,
    ¬ @Equation1780 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1793 takes them (3 nodes). -/
def ordS8R130_Law1793 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1793. -/
theorem noS8R130_Law1793 : ∀ v : Magma.tup8R130,
    ¬ @Equation1793 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1793) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1793) (by native_decide) v.1 v.2
    ((@Law1793.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1833 takes them (3 nodes). -/
def ordS8R130_Law1833 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1833. -/
theorem noS8R130_Law1833 : ∀ v : Magma.tup8R130,
    ¬ @Equation1833 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1833) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1833) (by native_decide) v.1 v.2
    ((@Law1833.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1835 takes them (3 nodes). -/
def ordS8R130_Law1835 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1835. -/
theorem noS8R130_Law1835 : ∀ v : Magma.tup8R130,
    ¬ @Equation1835 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1835) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1835) (by native_decide) v.1 v.2
    ((@Law1835.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1837 takes them (4 nodes). -/
def ordS8R130_Law1837 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1837. -/
theorem noS8R130_Law1837 : ∀ v : Magma.tup8R130,
    ¬ @Equation1837 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1837) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1837) (by native_decide) v.1 v.2
    ((@Law1837.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (3 nodes). -/
def ordS8R130_Law1838 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1838. -/
theorem noS8R130_Law1838 : ∀ v : Magma.tup8R130,
    ¬ @Equation1838 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1839 takes them (3 nodes). -/
def ordS8R130_Law1839 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1839. -/
theorem noS8R130_Law1839 : ∀ v : Magma.tup8R130,
    ¬ @Equation1839 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1839) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1839) (by native_decide) v.1 v.2
    ((@Law1839.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (4 nodes). -/
def ordS8R130_Law1840 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1840. -/
theorem noS8R130_Law1840 : ∀ v : Magma.tup8R130,
    ¬ @Equation1840 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1847 takes them (4 nodes). -/
def ordS8R130_Law1847 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1847. -/
theorem noS8R130_Law1847 : ∀ v : Magma.tup8R130,
    ¬ @Equation1847 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1847) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1847) (by native_decide) v.1 v.2
    ((@Law1847.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (3 nodes). -/
def ordS8R130_Law1848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1848. -/
theorem noS8R130_Law1848 : ∀ v : Magma.tup8R130,
    ¬ @Equation1848 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1850 takes them (4 nodes). -/
def ordS8R130_Law1850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1850. -/
theorem noS8R130_Law1850 : ∀ v : Magma.tup8R130,
    ¬ @Equation1850 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1850) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1850) (by native_decide) v.1 v.2
    ((@Law1850.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1857 takes them (4 nodes). -/
def ordS8R130_Law1857 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1857. -/
theorem noS8R130_Law1857 : ∀ v : Magma.tup8R130,
    ¬ @Equation1857 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1857) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1857) (by native_decide) v.1 v.2
    ((@Law1857.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (3 nodes). -/
def ordS8R130_Law1861 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1861. -/
theorem noS8R130_Law1861 : ∀ v : Magma.tup8R130,
    ¬ @Equation1861 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1865 takes them (3 nodes). -/
def ordS8R130_Law1865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1865. -/
theorem noS8R130_Law1865 : ∀ v : Magma.tup8R130,
    ¬ @Equation1865 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1865) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1865) (by native_decide) v.1 v.2
    ((@Law1865.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (3 nodes). -/
def ordS8R130_Law1873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1873. -/
theorem noS8R130_Law1873 : ∀ v : Magma.tup8R130,
    ¬ @Equation1873 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1876 takes them (3 nodes). -/
def ordS8R130_Law1876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1876. -/
theorem noS8R130_Law1876 : ∀ v : Magma.tup8R130,
    ¬ @Equation1876 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1876) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1876) (by native_decide) v.1 v.2
    ((@Law1876.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1884 takes them (3 nodes). -/
def ordS8R130_Law1884 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1884. -/
theorem noS8R130_Law1884 : ∀ v : Magma.tup8R130,
    ¬ @Equation1884 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1884) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1884) (by native_decide) v.1 v.2
    ((@Law1884.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1887 takes them (3 nodes). -/
def ordS8R130_Law1887 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1887. -/
theorem noS8R130_Law1887 : ∀ v : Magma.tup8R130,
    ¬ @Equation1887 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1887) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1887) (by native_decide) v.1 v.2
    ((@Law1887.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (3 nodes). -/
def ordS8R130_Law1894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1894. -/
theorem noS8R130_Law1894 : ∀ v : Magma.tup8R130,
    ¬ @Equation1894 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (3 nodes). -/
def ordS8R130_Law1921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1921. -/
theorem noS8R130_Law1921 : ∀ v : Magma.tup8R130,
    ¬ @Equation1921 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (3 nodes). -/
def ordS8R130_Law1934 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1934. -/
theorem noS8R130_Law1934 : ∀ v : Magma.tup8R130,
    ¬ @Equation1934 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (3 nodes). -/
def ordS8R130_Law1949 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1949. -/
theorem noS8R130_Law1949 : ∀ v : Magma.tup8R130,
    ¬ @Equation1949 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1983 takes them (3 nodes). -/
def ordS8R130_Law1983 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1983. -/
theorem noS8R130_Law1983 : ∀ v : Magma.tup8R130,
    ¬ @Equation1983 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1983) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1983) (by native_decide) v.1 v.2
    ((@Law1983.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1996 takes them (3 nodes). -/
def ordS8R130_Law1996 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1996. -/
theorem noS8R130_Law1996 : ∀ v : Magma.tup8R130,
    ¬ @Equation1996 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1996) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1996) (by native_decide) v.1 v.2
    ((@Law1996.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2036 takes them (3 nodes). -/
def ordS8R130_Law2036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2036. -/
theorem noS8R130_Law2036 : ∀ v : Magma.tup8R130,
    ¬ @Equation2036 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2036) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2036) (by native_decide) v.1 v.2
    ((@Law2036.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2038 takes them (3 nodes). -/
def ordS8R130_Law2038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2038. -/
theorem noS8R130_Law2038 : ∀ v : Magma.tup8R130,
    ¬ @Equation2038 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2038) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2038) (by native_decide) v.1 v.2
    ((@Law2038.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2041 takes them (3 nodes). -/
def ordS8R130_Law2041 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2041. -/
theorem noS8R130_Law2041 : ∀ v : Magma.tup8R130,
    ¬ @Equation2041 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2041) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2041) (by native_decide) v.1 v.2
    ((@Law2041.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2044 takes them (3 nodes). -/
def ordS8R130_Law2044 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2044. -/
theorem noS8R130_Law2044 : ∀ v : Magma.tup8R130,
    ¬ @Equation2044 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2044) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2044) (by native_decide) v.1 v.2
    ((@Law2044.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2050 takes them (4 nodes). -/
def ordS8R130_Law2050 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2050. -/
theorem noS8R130_Law2050 : ∀ v : Magma.tup8R130,
    ¬ @Equation2050 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2050) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2050) (by native_decide) v.1 v.2
    ((@Law2050.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (3 nodes). -/
def ordS8R130_Law2051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2051. -/
theorem noS8R130_Law2051 : ∀ v : Magma.tup8R130,
    ¬ @Equation2051 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (4 nodes). -/
def ordS8R130_Law2053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2053. -/
theorem noS8R130_Law2053 : ∀ v : Magma.tup8R130,
    ¬ @Equation2053 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (4 nodes). -/
def ordS8R130_Law2060 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2060. -/
theorem noS8R130_Law2060 : ∀ v : Magma.tup8R130,
    ¬ @Equation2060 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2063 takes them (4 nodes). -/
def ordS8R130_Law2063 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2063. -/
theorem noS8R130_Law2063 : ∀ v : Magma.tup8R130,
    ¬ @Equation2063 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2063) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2063) (by native_decide) v.1 v.2
    ((@Law2063.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (3 nodes). -/
def ordS8R130_Law2064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2064. -/
theorem noS8R130_Law2064 : ∀ v : Magma.tup8R130,
    ¬ @Equation2064 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2068 takes them (3 nodes). -/
def ordS8R130_Law2068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2068. -/
theorem noS8R130_Law2068 : ∀ v : Magma.tup8R130,
    ¬ @Equation2068 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2068) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2068) (by native_decide) v.1 v.2
    ((@Law2068.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2076 takes them (3 nodes). -/
def ordS8R130_Law2076 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2076. -/
theorem noS8R130_Law2076 : ∀ v : Magma.tup8R130,
    ¬ @Equation2076 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2076) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2076) (by native_decide) v.1 v.2
    ((@Law2076.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_2 :
    FamilyRefutes Magma.srch8R130 [
      1252, 1253, 1254, 1255, 1256, 1257, 1258, 1264, 1267, 1278, 1325, 1340, 1374, 1387, 1427,
      1428, 1429, 1430, 1432, 1434, 1442, 1444, 1454, 1455, 1459, 1467, 1470, 1478, 1481, 1488,
      1515, 1525, 1528, 1543, 1577, 1590, 1630, 1631, 1632, 1634, 1635, 1637, 1645, 1647, 1654,
      1658, 1662, 1670, 1673, 1681, 1684, 1691, 1701, 1718, 1731, 1746, 1780, 1793, 1833, 1835,
      1837, 1838, 1839, 1840, 1847, 1848, 1850, 1857, 1861, 1865, 1873, 1876, 1884, 1887, 1894,
      1921, 1934, 1949, 1983, 1996, 2036, 2038, 2041, 2044, 2050, 2051, 2053, 2060, 2063, 2064,
      2068, 2076
    ] :=
  ⟨noS8R130_Law1252, noS8R130_Law1253, noS8R130_Law1254, noS8R130_Law1255, noS8R130_Law1256, noS8R130_Law1257, noS8R130_Law1258, noS8R130_Law1264, noS8R130_Law1267, noS8R130_Law1278, noS8R130_Law1325, noS8R130_Law1340, noS8R130_Law1374, noS8R130_Law1387, noS8R130_Law1427, noS8R130_Law1428, noS8R130_Law1429, noS8R130_Law1430, noS8R130_Law1432, noS8R130_Law1434, noS8R130_Law1442, noS8R130_Law1444, noS8R130_Law1454, noS8R130_Law1455, noS8R130_Law1459, noS8R130_Law1467, noS8R130_Law1470, noS8R130_Law1478, noS8R130_Law1481, noS8R130_Law1488, noS8R130_Law1515, noS8R130_Law1525, noS8R130_Law1528, noS8R130_Law1543, noS8R130_Law1577, noS8R130_Law1590, noS8R130_Law1630, noS8R130_Law1631, noS8R130_Law1632, noS8R130_Law1634, noS8R130_Law1635, noS8R130_Law1637, noS8R130_Law1645, noS8R130_Law1647, noS8R130_Law1654, noS8R130_Law1658, noS8R130_Law1662, noS8R130_Law1670, noS8R130_Law1673, noS8R130_Law1681, noS8R130_Law1684, noS8R130_Law1691, noS8R130_Law1701, noS8R130_Law1718, noS8R130_Law1731, noS8R130_Law1746, noS8R130_Law1780, noS8R130_Law1793, noS8R130_Law1833, noS8R130_Law1835, noS8R130_Law1837, noS8R130_Law1838, noS8R130_Law1839, noS8R130_Law1840, noS8R130_Law1847, noS8R130_Law1848, noS8R130_Law1850, noS8R130_Law1857, noS8R130_Law1861, noS8R130_Law1865, noS8R130_Law1873, noS8R130_Law1876, noS8R130_Law1884, noS8R130_Law1887, noS8R130_Law1894, noS8R130_Law1921, noS8R130_Law1934, noS8R130_Law1949, noS8R130_Law1983, noS8R130_Law1996, noS8R130_Law2036, noS8R130_Law2038, noS8R130_Law2041, noS8R130_Law2044, noS8R130_Law2050, noS8R130_Law2051, noS8R130_Law2053, noS8R130_Law2060, noS8R130_Law2063, noS8R130_Law2064, noS8R130_Law2068, noS8R130_Law2076⟩

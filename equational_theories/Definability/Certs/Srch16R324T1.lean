import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate targets: `Magma.srch16R324` (part 2 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R324_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 351 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1184 takes them (3 nodes). -/
def ordS16R324_Law1184 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1184. -/
theorem noS16R324_Law1184 : ∀ v : Magma.tup16R324,
    ¬ @Equation1184 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (3 nodes). -/
def ordS16R324_Law1226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1226. -/
theorem noS16R324_Law1226 : ∀ v : Magma.tup16R324,
    ¬ @Equation1226 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (3 nodes). -/
def ordS16R324_Law1229 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1229. -/
theorem noS16R324_Law1229 : ∀ v : Magma.tup16R324,
    ¬ @Equation1229 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (4 nodes). -/
def ordS16R324_Law1231 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1231. -/
theorem noS16R324_Law1231 : ∀ v : Magma.tup16R324,
    ¬ @Equation1231 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1232 takes them (5 nodes). -/
def ordS16R324_Law1232 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1232. -/
theorem noS16R324_Law1232 : ∀ v : Magma.tup16R324,
    ¬ @Equation1232 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1232) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1232) (by native_decide) v.1 v.2
    ((@Law1232.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (3 nodes). -/
def ordS16R324_Law1239 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1239. -/
theorem noS16R324_Law1239 : ∀ v : Magma.tup16R324,
    ¬ @Equation1239 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1241 takes them (6 nodes). -/
def ordS16R324_Law1241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1241. -/
theorem noS16R324_Law1241 : ∀ v : Magma.tup16R324,
    ¬ @Equation1241 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1241) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1241) (by native_decide) v.1 v.2
    ((@Law1241.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (3 nodes). -/
def ordS16R324_Law1242 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1242. -/
theorem noS16R324_Law1242 : ∀ v : Magma.tup16R324,
    ¬ @Equation1242 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (5 nodes). -/
def ordS16R324_Law1249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1249. -/
theorem noS16R324_Law1249 : ∀ v : Magma.tup16R324,
    ¬ @Equation1249 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (3 nodes). -/
def ordS16R324_Law1278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1278. -/
theorem noS16R324_Law1278 : ∀ v : Magma.tup16R324,
    ¬ @Equation1278 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1288 takes them (5 nodes). -/
def ordS16R324_Law1288 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1288. -/
theorem noS16R324_Law1288 : ∀ v : Magma.tup16R324,
    ¬ @Equation1288 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1288) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1288) (by native_decide) v.1 v.2
    ((@Law1288.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (3 nodes). -/
def ordS16R324_Law1312 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1312. -/
theorem noS16R324_Law1312 : ∀ v : Magma.tup16R324,
    ¬ @Equation1312 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1315 takes them (3 nodes). -/
def ordS16R324_Law1315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1315. -/
theorem noS16R324_Law1315 : ∀ v : Magma.tup16R324,
    ¬ @Equation1315 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1315) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1315) (by native_decide) v.1 v.2
    ((@Law1315.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1316 takes them (4 nodes). -/
def ordS16R324_Law1316 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1316. -/
theorem noS16R324_Law1316 : ∀ v : Magma.tup16R324,
    ¬ @Equation1316 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1316) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1316) (by native_decide) v.1 v.2
    ((@Law1316.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1322 takes them (5 nodes). -/
def ordS16R324_Law1322 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1322. -/
theorem noS16R324_Law1322 : ∀ v : Magma.tup16R324,
    ¬ @Equation1322 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1322) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1322) (by native_decide) v.1 v.2
    ((@Law1322.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (3 nodes). -/
def ordS16R324_Law1325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1325. -/
theorem noS16R324_Law1325 : ∀ v : Magma.tup16R324,
    ¬ @Equation1325 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1432 takes them (5 nodes). -/
def ordS16R324_Law1432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1432. -/
theorem noS16R324_Law1432 : ∀ v : Magma.tup16R324,
    ¬ @Equation1432 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1432) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1432) (by native_decide) v.1 v.2
    ((@Law1432.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1434 takes them (4 nodes). -/
def ordS16R324_Law1434 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1434. -/
theorem noS16R324_Law1434 : ∀ v : Magma.tup16R324,
    ¬ @Equation1434 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1434) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1434) (by native_decide) v.1 v.2
    ((@Law1434.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (5 nodes). -/
def ordS16R324_Law1442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1442. -/
theorem noS16R324_Law1442 : ∀ v : Magma.tup16R324,
    ¬ @Equation1442 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (4 nodes). -/
def ordS16R324_Law1444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1444. -/
theorem noS16R324_Law1444 : ∀ v : Magma.tup16R324,
    ¬ @Equation1444 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1452 takes them (3 nodes). -/
def ordS16R324_Law1452 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1452. -/
theorem noS16R324_Law1452 : ∀ v : Magma.tup16R324,
    ¬ @Equation1452 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1452) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1452) (by native_decide) v.1 v.2
    ((@Law1452.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1454 takes them (4 nodes). -/
def ordS16R324_Law1454 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1454. -/
theorem noS16R324_Law1454 : ∀ v : Magma.tup16R324,
    ¬ @Equation1454 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1454) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1454) (by native_decide) v.1 v.2
    ((@Law1454.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (3 nodes). -/
def ordS16R324_Law1455 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1455. -/
theorem noS16R324_Law1455 : ∀ v : Magma.tup16R324,
    ¬ @Equation1455 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (5 nodes). -/
def ordS16R324_Law1481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1481. -/
theorem noS16R324_Law1481 : ∀ v : Magma.tup16R324,
    ¬ @Equation1481 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1491 takes them (3 nodes). -/
def ordS16R324_Law1491 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1491. -/
theorem noS16R324_Law1491 : ∀ v : Magma.tup16R324,
    ¬ @Equation1491 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1491) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1491) (by native_decide) v.1 v.2
    ((@Law1491.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1518 takes them (3 nodes). -/
def ordS16R324_Law1518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1518. -/
theorem noS16R324_Law1518 : ∀ v : Magma.tup16R324,
    ¬ @Equation1518 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1518) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1518) (by native_decide) v.1 v.2
    ((@Law1518.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1519 takes them (4 nodes). -/
def ordS16R324_Law1519 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1519. -/
theorem noS16R324_Law1519 : ∀ v : Magma.tup16R324,
    ¬ @Equation1519 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1519) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1519) (by native_decide) v.1 v.2
    ((@Law1519.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1525 takes them (3 nodes). -/
def ordS16R324_Law1525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1525. -/
theorem noS16R324_Law1525 : ∀ v : Magma.tup16R324,
    ¬ @Equation1525 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1525) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1525) (by native_decide) v.1 v.2
    ((@Law1525.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (5 nodes). -/
def ordS16R324_Law1528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1528. -/
theorem noS16R324_Law1528 : ∀ v : Magma.tup16R324,
    ¬ @Equation1528 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (3 nodes). -/
def ordS16R324_Law1632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1632. -/
theorem noS16R324_Law1632 : ∀ v : Magma.tup16R324,
    ¬ @Equation1632 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (5 nodes). -/
def ordS16R324_Law1635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1635. -/
theorem noS16R324_Law1635 : ∀ v : Magma.tup16R324,
    ¬ @Equation1635 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1647 takes them (4 nodes). -/
def ordS16R324_Law1647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1647. -/
theorem noS16R324_Law1647 : ∀ v : Magma.tup16R324,
    ¬ @Equation1647 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1647) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1647) (by native_decide) v.1 v.2
    ((@Law1647.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1648 takes them (5 nodes). -/
def ordS16R324_Law1648 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1648. -/
theorem noS16R324_Law1648 : ∀ v : Magma.tup16R324,
    ¬ @Equation1648 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1648) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1648) (by native_decide) v.1 v.2
    ((@Law1648.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (4 nodes). -/
def ordS16R324_Law1654 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1654. -/
theorem noS16R324_Law1654 : ∀ v : Magma.tup16R324,
    ¬ @Equation1654 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1655 takes them (3 nodes). -/
def ordS16R324_Law1655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1655. -/
theorem noS16R324_Law1655 : ∀ v : Magma.tup16R324,
    ¬ @Equation1655 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1655) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1655) (by native_decide) v.1 v.2
    ((@Law1655.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (3 nodes). -/
def ordS16R324_Law1658 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1658. -/
theorem noS16R324_Law1658 : ∀ v : Magma.tup16R324,
    ¬ @Equation1658 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (3 nodes). -/
def ordS16R324_Law1662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1662. -/
theorem noS16R324_Law1662 : ∀ v : Magma.tup16R324,
    ¬ @Equation1662 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (5 nodes). -/
def ordS16R324_Law1684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1684. -/
theorem noS16R324_Law1684 : ∀ v : Magma.tup16R324,
    ¬ @Equation1684 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (3 nodes). -/
def ordS16R324_Law1691 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1691. -/
theorem noS16R324_Law1691 : ∀ v : Magma.tup16R324,
    ¬ @Equation1691 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1721 takes them (3 nodes). -/
def ordS16R324_Law1721 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1721. -/
theorem noS16R324_Law1721 : ∀ v : Magma.tup16R324,
    ¬ @Equation1721 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1721) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1721) (by native_decide) v.1 v.2
    ((@Law1721.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1728 takes them (5 nodes). -/
def ordS16R324_Law1728 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1728. -/
theorem noS16R324_Law1728 : ∀ v : Magma.tup16R324,
    ¬ @Equation1728 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1728) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1728) (by native_decide) v.1 v.2
    ((@Law1728.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (3 nodes). -/
def ordS16R324_Law1731 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1731. -/
theorem noS16R324_Law1731 : ∀ v : Magma.tup16R324,
    ¬ @Equation1731 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (3 nodes). -/
def ordS16R324_Law1780 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1780. -/
theorem noS16R324_Law1780 : ∀ v : Magma.tup16R324,
    ¬ @Equation1780 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (3 nodes). -/
def ordS16R324_Law1838 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1838. -/
theorem noS16R324_Law1838 : ∀ v : Magma.tup16R324,
    ¬ @Equation1838 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (4 nodes). -/
def ordS16R324_Law1840 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1840. -/
theorem noS16R324_Law1840 : ∀ v : Magma.tup16R324,
    ¬ @Equation1840 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1841 takes them (5 nodes). -/
def ordS16R324_Law1841 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1841. -/
theorem noS16R324_Law1841 : ∀ v : Magma.tup16R324,
    ¬ @Equation1841 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1841) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1841) (by native_decide) v.1 v.2
    ((@Law1841.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (5 nodes). -/
def ordS16R324_Law1848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1848. -/
theorem noS16R324_Law1848 : ∀ v : Magma.tup16R324,
    ¬ @Equation1848 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1850 takes them (4 nodes). -/
def ordS16R324_Law1850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1850. -/
theorem noS16R324_Law1850 : ∀ v : Magma.tup16R324,
    ¬ @Equation1850 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1850) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1850) (by native_decide) v.1 v.2
    ((@Law1850.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1851 takes them (3 nodes). -/
def ordS16R324_Law1851 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1851. -/
theorem noS16R324_Law1851 : ∀ v : Magma.tup16R324,
    ¬ @Equation1851 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1851) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1851) (by native_decide) v.1 v.2
    ((@Law1851.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (3 nodes). -/
def ordS16R324_Law1861 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1861. -/
theorem noS16R324_Law1861 : ∀ v : Magma.tup16R324,
    ¬ @Equation1861 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (3 nodes). -/
def ordS16R324_Law1873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1873. -/
theorem noS16R324_Law1873 : ∀ v : Magma.tup16R324,
    ¬ @Equation1873 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (5 nodes). -/
def ordS16R324_Law1894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1894. -/
theorem noS16R324_Law1894 : ∀ v : Magma.tup16R324,
    ¬ @Equation1894 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (3 nodes). -/
def ordS16R324_Law1897 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1897. -/
theorem noS16R324_Law1897 : ∀ v : Magma.tup16R324,
    ¬ @Equation1897 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (3 nodes). -/
def ordS16R324_Law1921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1921. -/
theorem noS16R324_Law1921 : ∀ v : Magma.tup16R324,
    ¬ @Equation1921 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1924 takes them (5 nodes). -/
def ordS16R324_Law1924 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1924. -/
theorem noS16R324_Law1924 : ∀ v : Magma.tup16R324,
    ¬ @Equation1924 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1924) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1924) (by native_decide) v.1 v.2
    ((@Law1924.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (3 nodes). -/
def ordS16R324_Law1934 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1934. -/
theorem noS16R324_Law1934 : ∀ v : Magma.tup16R324,
    ¬ @Equation1934 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (3 nodes). -/
def ordS16R324_Law1949 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1949. -/
theorem noS16R324_Law1949 : ∀ v : Magma.tup16R324,
    ¬ @Equation1949 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2044 takes them (3 nodes). -/
def ordS16R324_Law2044 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2044. -/
theorem noS16R324_Law2044 : ∀ v : Magma.tup16R324,
    ¬ @Equation2044 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2044) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2044) (by native_decide) v.1 v.2
    ((@Law2044.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (5 nodes). -/
def ordS16R324_Law2051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2051. -/
theorem noS16R324_Law2051 : ∀ v : Magma.tup16R324,
    ¬ @Equation2051 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (4 nodes). -/
def ordS16R324_Law2053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2053. -/
theorem noS16R324_Law2053 : ∀ v : Magma.tup16R324,
    ¬ @Equation2053 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2054 takes them (3 nodes). -/
def ordS16R324_Law2054 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2054. -/
theorem noS16R324_Law2054 : ∀ v : Magma.tup16R324,
    ¬ @Equation2054 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2054) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2054) (by native_decide) v.1 v.2
    ((@Law2054.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (4 nodes). -/
def ordS16R324_Law2060 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2060. -/
theorem noS16R324_Law2060 : ∀ v : Magma.tup16R324,
    ¬ @Equation2060 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2061 takes them (3 nodes). -/
def ordS16R324_Law2061 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2061. -/
theorem noS16R324_Law2061 : ∀ v : Magma.tup16R324,
    ¬ @Equation2061 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2061) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2061) (by native_decide) v.1 v.2
    ((@Law2061.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2063 takes them (4 nodes). -/
def ordS16R324_Law2063 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2063. -/
theorem noS16R324_Law2063 : ∀ v : Magma.tup16R324,
    ¬ @Equation2063 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2063) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2063) (by native_decide) v.1 v.2
    ((@Law2063.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (5 nodes). -/
def ordS16R324_Law2064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2064. -/
theorem noS16R324_Law2064 : ∀ v : Magma.tup16R324,
    ¬ @Equation2064 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (5 nodes). -/
def ordS16R324_Law2090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2090. -/
theorem noS16R324_Law2090 : ∀ v : Magma.tup16R324,
    ¬ @Equation2090 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2097 takes them (5 nodes). -/
def ordS16R324_Law2097 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2097. -/
theorem noS16R324_Law2097 : ∀ v : Magma.tup16R324,
    ¬ @Equation2097 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2097) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2097) (by native_decide) v.1 v.2
    ((@Law2097.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2100 takes them (3 nodes). -/
def ordS16R324_Law2100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2100. -/
theorem noS16R324_Law2100 : ∀ v : Magma.tup16R324,
    ¬ @Equation2100 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2100) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2100) (by native_decide) v.1 v.2
    ((@Law2100.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2128 takes them (4 nodes). -/
def ordS16R324_Law2128 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2128. -/
theorem noS16R324_Law2128 : ∀ v : Magma.tup16R324,
    ¬ @Equation2128 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2128) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2128) (by native_decide) v.1 v.2
    ((@Law2128.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (3 nodes). -/
def ordS16R324_Law2137 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2137. -/
theorem noS16R324_Law2137 : ∀ v : Magma.tup16R324,
    ¬ @Equation2137 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2241 takes them (3 nodes). -/
def ordS16R324_Law2241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2241. -/
theorem noS16R324_Law2241 : ∀ v : Magma.tup16R324,
    ¬ @Equation2241 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2247 takes them (5 nodes). -/
def ordS16R324_Law2247 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2247. -/
theorem noS16R324_Law2247 : ∀ v : Magma.tup16R324,
    ¬ @Equation2247 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2247) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2247) (by native_decide) v.1 v.2
    ((@Law2247.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (3 nodes). -/
def ordS16R324_Law2254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2254. -/
theorem noS16R324_Law2254 : ∀ v : Magma.tup16R324,
    ¬ @Equation2254 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2256 takes them (6 nodes). -/
def ordS16R324_Law2256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2256. -/
theorem noS16R324_Law2256 : ∀ v : Magma.tup16R324,
    ¬ @Equation2256 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2256) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2256) (by native_decide) v.1 v.2
    ((@Law2256.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2257 takes them (3 nodes). -/
def ordS16R324_Law2257 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2257. -/
theorem noS16R324_Law2257 : ∀ v : Magma.tup16R324,
    ¬ @Equation2257 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2257) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2257) (by native_decide) v.1 v.2
    ((@Law2257.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (4 nodes). -/
def ordS16R324_Law2263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2263. -/
theorem noS16R324_Law2263 : ∀ v : Magma.tup16R324,
    ¬ @Equation2263 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2264 takes them (5 nodes). -/
def ordS16R324_Law2264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2264. -/
theorem noS16R324_Law2264 : ∀ v : Magma.tup16R324,
    ¬ @Equation2264 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2264) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2264) (by native_decide) v.1 v.2
    ((@Law2264.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (3 nodes). -/
def ordS16R324_Law2267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2267. -/
theorem noS16R324_Law2267 : ∀ v : Magma.tup16R324,
    ¬ @Equation2267 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (3 nodes). -/
def ordS16R324_Law2293 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2293. -/
theorem noS16R324_Law2293 : ∀ v : Magma.tup16R324,
    ¬ @Equation2293 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (3 nodes). -/
def ordS16R324_Law2300 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2300. -/
theorem noS16R324_Law2300 : ∀ v : Magma.tup16R324,
    ¬ @Equation2300 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (5 nodes). -/
def ordS16R324_Law2303 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2303. -/
theorem noS16R324_Law2303 : ∀ v : Magma.tup16R324,
    ¬ @Equation2303 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (3 nodes). -/
def ordS16R324_Law2327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2327. -/
theorem noS16R324_Law2327 : ∀ v : Magma.tup16R324,
    ¬ @Equation2327 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (3 nodes). -/
def ordS16R324_Law2330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2330. -/
theorem noS16R324_Law2330 : ∀ v : Magma.tup16R324,
    ¬ @Equation2330 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2331 takes them (4 nodes). -/
def ordS16R324_Law2331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2331. -/
theorem noS16R324_Law2331 : ∀ v : Magma.tup16R324,
    ¬ @Equation2331 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2331) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2331) (by native_decide) v.1 v.2
    ((@Law2331.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2337 takes them (5 nodes). -/
def ordS16R324_Law2337 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2337. -/
theorem noS16R324_Law2337 : ∀ v : Magma.tup16R324,
    ¬ @Equation2337 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2337) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2337) (by native_decide) v.1 v.2
    ((@Law2337.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (5 nodes). -/
def ordS16R324_Law2444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2444. -/
theorem noS16R324_Law2444 : ∀ v : Magma.tup16R324,
    ¬ @Equation2444 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2447 takes them (3 nodes). -/
def ordS16R324_Law2447 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2447. -/
theorem noS16R324_Law2447 : ∀ v : Magma.tup16R324,
    ¬ @Equation2447 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2447) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2447) (by native_decide) v.1 v.2
    ((@Law2447.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (4 nodes). -/
def ordS16R324_Law2449 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2449. -/
theorem noS16R324_Law2449 : ∀ v : Magma.tup16R324,
    ¬ @Equation2449 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2450 takes them (3 nodes). -/
def ordS16R324_Law2450 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2450. -/
theorem noS16R324_Law2450 : ∀ v : Magma.tup16R324,
    ¬ @Equation2450 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2450) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2450) (by native_decide) v.1 v.2
    ((@Law2450.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (5 nodes). -/
def ordS16R324_Law2457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2457. -/
theorem noS16R324_Law2457 : ∀ v : Magma.tup16R324,
    ¬ @Equation2457 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2459 takes them (6 nodes). -/
def ordS16R324_Law2459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2459. -/
theorem noS16R324_Law2459 : ∀ v : Magma.tup16R324,
    ¬ @Equation2459 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2459) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2459) (by native_decide) v.1 v.2
    ((@Law2459.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch16R324_refutes_1 :
    FamilyRefutes Magma.srch16R324 [
      1184, 1226, 1229, 1231, 1232, 1239, 1241, 1242, 1249, 1278, 1288, 1312, 1315, 1316, 1322,
      1325, 1432, 1434, 1442, 1444, 1452, 1454, 1455, 1481, 1491, 1518, 1519, 1525, 1528, 1632,
      1635, 1647, 1648, 1654, 1655, 1658, 1662, 1684, 1691, 1721, 1728, 1731, 1780, 1838, 1840,
      1841, 1848, 1850, 1851, 1861, 1873, 1894, 1897, 1921, 1924, 1934, 1949, 2044, 2051, 2053,
      2054, 2060, 2061, 2063, 2064, 2090, 2097, 2100, 2128, 2137, 2241, 2247, 2254, 2256, 2257,
      2263, 2264, 2267, 2293, 2300, 2303, 2327, 2330, 2331, 2337, 2444, 2447, 2449, 2450, 2457,
      2459
    ] :=
  ⟨noS16R324_Law1184, noS16R324_Law1226, noS16R324_Law1229, noS16R324_Law1231, noS16R324_Law1232, noS16R324_Law1239, noS16R324_Law1241, noS16R324_Law1242, noS16R324_Law1249, noS16R324_Law1278, noS16R324_Law1288, noS16R324_Law1312, noS16R324_Law1315, noS16R324_Law1316, noS16R324_Law1322, noS16R324_Law1325, noS16R324_Law1432, noS16R324_Law1434, noS16R324_Law1442, noS16R324_Law1444, noS16R324_Law1452, noS16R324_Law1454, noS16R324_Law1455, noS16R324_Law1481, noS16R324_Law1491, noS16R324_Law1518, noS16R324_Law1519, noS16R324_Law1525, noS16R324_Law1528, noS16R324_Law1632, noS16R324_Law1635, noS16R324_Law1647, noS16R324_Law1648, noS16R324_Law1654, noS16R324_Law1655, noS16R324_Law1658, noS16R324_Law1662, noS16R324_Law1684, noS16R324_Law1691, noS16R324_Law1721, noS16R324_Law1728, noS16R324_Law1731, noS16R324_Law1780, noS16R324_Law1838, noS16R324_Law1840, noS16R324_Law1841, noS16R324_Law1848, noS16R324_Law1850, noS16R324_Law1851, noS16R324_Law1861, noS16R324_Law1873, noS16R324_Law1894, noS16R324_Law1897, noS16R324_Law1921, noS16R324_Law1924, noS16R324_Law1934, noS16R324_Law1949, noS16R324_Law2044, noS16R324_Law2051, noS16R324_Law2053, noS16R324_Law2054, noS16R324_Law2060, noS16R324_Law2061, noS16R324_Law2063, noS16R324_Law2064, noS16R324_Law2090, noS16R324_Law2097, noS16R324_Law2100, noS16R324_Law2128, noS16R324_Law2137, noS16R324_Law2241, noS16R324_Law2247, noS16R324_Law2254, noS16R324_Law2256, noS16R324_Law2257, noS16R324_Law2263, noS16R324_Law2264, noS16R324_Law2267, noS16R324_Law2293, noS16R324_Law2300, noS16R324_Law2303, noS16R324_Law2327, noS16R324_Law2330, noS16R324_Law2331, noS16R324_Law2337, noS16R324_Law2444, noS16R324_Law2447, noS16R324_Law2449, noS16R324_Law2450, noS16R324_Law2457, noS16R324_Law2459⟩

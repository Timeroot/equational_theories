import equational_theories.Definability.Srch_S8R113

/-!
# Structural certificate targets: `Magma.srch8R113`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R113_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `48` equations here, 624 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R113_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 117 takes them (15 nodes). -/
def ordS8R113_Law117 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 117. -/
theorem noS8R113_Law117 : ∀ v : Magma.tup8R113,
    ¬ @Equation117 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law117) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law117) (by native_decide) v.1 v.2
    ((@Law117.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 127 takes them (13 nodes). -/
def ordS8R113_Law127 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 127. -/
theorem noS8R113_Law127 : ∀ v : Magma.tup8R113,
    ¬ @Equation127 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (13 nodes). -/
def ordS8R113_Law160 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 160. -/
theorem noS8R113_Law160 : ∀ v : Magma.tup8R113,
    ¬ @Equation160 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (13 nodes). -/
def ordS8R113_Law179 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 179. -/
theorem noS8R113_Law179 : ∀ v : Magma.tup8R113,
    ¬ @Equation179 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 209 takes them (15 nodes). -/
def ordS8R113_Law209 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 209. -/
theorem noS8R113_Law209 : ∀ v : Magma.tup8R113,
    ¬ @Equation209 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law209) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law209) (by native_decide) v.1 v.2
    ((@Law209.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (13 nodes). -/
def ordS8R113_Law212 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 212. -/
theorem noS8R113_Law212 : ∀ v : Magma.tup8R113,
    ¬ @Equation212 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (16 nodes). -/
def ordS8R113_Law466 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 466. -/
theorem noS8R113_Law466 : ∀ v : Magma.tup8R113,
    ¬ @Equation466 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (15 nodes). -/
def ordS8R113_Law473 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 473. -/
theorem noS8R113_Law473 : ∀ v : Magma.tup8R113,
    ¬ @Equation473 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (13 nodes). -/
def ordS8R113_Law500 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 500. -/
theorem noS8R113_Law500 : ∀ v : Magma.tup8R113,
    ¬ @Equation500 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (13 nodes). -/
def ordS8R113_Law513 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 513. -/
theorem noS8R113_Law513 : ∀ v : Magma.tup8R113,
    ¬ @Equation513 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (13 nodes). -/
def ordS8R113_Law528 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 528. -/
theorem noS8R113_Law528 : ∀ v : Magma.tup8R113,
    ¬ @Equation528 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (13 nodes). -/
def ordS8R113_Law575 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 575. -/
theorem noS8R113_Law575 : ∀ v : Magma.tup8R113,
    ¬ @Equation575 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (15 nodes). -/
def ordS8R113_Law1075 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R113_Law1075 : ∀ v : Magma.tup8R113,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (13 nodes). -/
def ordS8R113_Law1278 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1278. -/
theorem noS8R113_Law1278 : ∀ v : Magma.tup8R113,
    ¬ @Equation1278 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1288 takes them (16 nodes). -/
def ordS8R113_Law1288 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1288. -/
theorem noS8R113_Law1288 : ∀ v : Magma.tup8R113,
    ¬ @Equation1288 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1288) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1288) (by native_decide) v.1 v.2
    ((@Law1288.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (13 nodes). -/
def ordS8R113_Law1325 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1325. -/
theorem noS8R113_Law1325 : ∀ v : Magma.tup8R113,
    ¬ @Equation1325 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1370 takes them (13 nodes). -/
def ordS8R113_Law1370 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1370. -/
theorem noS8R113_Law1370 : ∀ v : Magma.tup8R113,
    ¬ @Equation1370 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1370) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law1370) (by native_decide) v.1 v.2
    ((@Law1370.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1452 takes them (13 nodes). -/
def ordS8R113_Law1452 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1452. -/
theorem noS8R113_Law1452 : ∀ v : Magma.tup8R113,
    ¬ @Equation1452 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1452) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1452) (by native_decide) v.1 v.2
    ((@Law1452.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1453 takes them (13 nodes). -/
def ordS8R113_Law1453 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1453. -/
theorem noS8R113_Law1453 : ∀ v : Magma.tup8R113,
    ¬ @Equation1453 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1453) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law1453) (by native_decide) v.1 v.2
    ((@Law1453.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (13 nodes). -/
def ordS8R113_Law1455 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1455. -/
theorem noS8R113_Law1455 : ∀ v : Magma.tup8R113,
    ¬ @Equation1455 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1456 takes them (13 nodes). -/
def ordS8R113_Law1456 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1456. -/
theorem noS8R113_Law1456 : ∀ v : Magma.tup8R113,
    ¬ @Equation1456 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1456) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law1456) (by native_decide) v.1 v.2
    ((@Law1456.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (7 nodes). -/
def ordS8R113_Law1481 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1481. -/
theorem noS8R113_Law1481 : ∀ v : Magma.tup8R113,
    ¬ @Equation1481 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (7 nodes). -/
def ordS8R113_Law2051 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2051. -/
theorem noS8R113_Law2051 : ∀ v : Magma.tup8R113,
    ¬ @Equation2051 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2100 takes them (13 nodes). -/
def ordS8R113_Law2100 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2100. -/
theorem noS8R113_Law2100 : ∀ v : Magma.tup8R113,
    ¬ @Equation2100 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2100) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2100) (by native_decide) v.1 v.2
    ((@Law2100.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2115 takes them (13 nodes). -/
def ordS8R113_Law2115 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2115. -/
theorem noS8R113_Law2115 : ∀ v : Magma.tup8R113,
    ¬ @Equation2115 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2115) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law2115) (by native_decide) v.1 v.2
    ((@Law2115.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (13 nodes). -/
def ordS8R113_Law2137 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2137. -/
theorem noS8R113_Law2137 : ∀ v : Magma.tup8R113,
    ¬ @Equation2137 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2203 takes them (13 nodes). -/
def ordS8R113_Law2203 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2203. -/
theorem noS8R113_Law2203 : ∀ v : Magma.tup8R113,
    ¬ @Equation2203 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2203) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law2203) (by native_decide) v.1 v.2
    ((@Law2203.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (13 nodes). -/
def ordS8R113_Law2254 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2254. -/
theorem noS8R113_Law2254 : ∀ v : Magma.tup8R113,
    ¬ @Equation2254 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2264 takes them (16 nodes). -/
def ordS8R113_Law2264 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2264. -/
theorem noS8R113_Law2264 : ∀ v : Magma.tup8R113,
    ¬ @Equation2264 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2264) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2264) (by native_decide) v.1 v.2
    ((@Law2264.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (13 nodes). -/
def ordS8R113_Law2267 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2267. -/
theorem noS8R113_Law2267 : ∀ v : Magma.tup8R113,
    ¬ @Equation2267 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2270 takes them (13 nodes). -/
def ordS8R113_Law2270 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2270. -/
theorem noS8R113_Law2270 : ∀ v : Magma.tup8R113,
    ¬ @Equation2270 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2270) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law2270) (by native_decide) v.1 v.2
    ((@Law2270.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (15 nodes). -/
def ordS8R113_Law2457 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R113_Law2457 : ∀ v : Magma.tup8R113,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (13 nodes). -/
def ordS8R113_Law3053 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3053. -/
theorem noS8R113_Law3053 : ∀ v : Magma.tup8R113,
    ¬ @Equation3053 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (15 nodes). -/
def ordS8R113_Law3056 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3056. -/
theorem noS8R113_Law3056 : ∀ v : Magma.tup8R113,
    ¬ @Equation3056 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (16 nodes). -/
def ordS8R113_Law3066 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R113_Law3066 : ∀ v : Magma.tup8R113,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (13 nodes). -/
def ordS8R113_Law3079 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3079. -/
theorem noS8R113_Law3079 : ∀ v : Magma.tup8R113,
    ¬ @Equation3079 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (13 nodes). -/
def ordS8R113_Law3083 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R113_Law3083 : ∀ v : Magma.tup8R113,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (13 nodes). -/
def ordS8R113_Law3094 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R113_Law3094 : ∀ v : Magma.tup8R113,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (13 nodes). -/
def ordS8R113_Law3518 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3518. -/
theorem noS8R113_Law3518 : ∀ v : Magma.tup8R113,
    ¬ @Equation3518 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (13 nodes). -/
def ordS8R113_Law3526 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3526. -/
theorem noS8R113_Law3526 : ∀ v : Magma.tup8R113,
    ¬ @Equation3526 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (7 nodes). -/
def ordS8R113_Law3549 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3549. -/
theorem noS8R113_Law3549 : ∀ v : Magma.tup8R113,
    ¬ @Equation3549 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (7 nodes). -/
def ordS8R113_Law3917 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3917. -/
theorem noS8R113_Law3917 : ∀ v : Magma.tup8R113,
    ¬ @Equation3917 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (13 nodes). -/
def ordS8R113_Law3962 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3962. -/
theorem noS8R113_Law3962 : ∀ v : Magma.tup8R113,
    ¬ @Equation3962 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (13 nodes). -/
def ordS8R113_Law4023 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4023. -/
theorem noS8R113_Law4023 : ∀ v : Magma.tup8R113,
    ¬ @Equation4023 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (13 nodes). -/
def ordS8R113_Law4275 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4275. -/
theorem noS8R113_Law4275 : ∀ v : Magma.tup8R113,
    ¬ @Equation4275 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (13 nodes). -/
def ordS8R113_Law4307 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4307. -/
theorem noS8R113_Law4307 : ∀ v : Magma.tup8R113,
    ¬ @Equation4307 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (13 nodes). -/
def ordS8R113_Law4585 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4585. -/
theorem noS8R113_Law4585 : ∀ v : Magma.tup8R113,
    ¬ @Equation4585 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 2)
    (ord := ordS8R113_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (13 nodes). -/
def ordS8R113_Law4656 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4656. -/
theorem noS8R113_Law4656 : ∀ v : Magma.tup8R113,
    ¬ @Equation4656 (Fin 8) (Magma.srch8R113 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S8R113.E) (tr := S8R113.tr) (z := S8R113.z)
    (st := S8R113.st) (X := S8R113.X) (envs := Magma.envsRed 8 S8R113.E 3)
    (ord := ordS8R113_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 8) (Magma.srch8R113 v)).mpr hv)

/-- No member of the class satisfies any of these `48` equations. -/
theorem srch8R113_refutes_0 :
    FamilyRefutes Magma.srch8R113 [
      117, 127, 160, 179, 209, 212, 466, 473, 500, 513, 528, 575, 1075, 1278, 1288, 1325, 1370,
      1452, 1453, 1455, 1456, 1481, 2051, 2100, 2115, 2137, 2203, 2254, 2264, 2267, 2270, 2457,
      3053, 3056, 3066, 3079, 3083, 3094, 3518, 3526, 3549, 3917, 3962, 4023, 4275, 4307, 4585,
      4656
    ] :=
  ⟨noS8R113_Law117, noS8R113_Law127, noS8R113_Law160, noS8R113_Law179, noS8R113_Law209, noS8R113_Law212, noS8R113_Law466, noS8R113_Law473, noS8R113_Law500, noS8R113_Law513, noS8R113_Law528, noS8R113_Law575, noS8R113_Law1075, noS8R113_Law1278, noS8R113_Law1288, noS8R113_Law1325, noS8R113_Law1370, noS8R113_Law1452, noS8R113_Law1453, noS8R113_Law1455, noS8R113_Law1456, noS8R113_Law1481, noS8R113_Law2051, noS8R113_Law2100, noS8R113_Law2115, noS8R113_Law2137, noS8R113_Law2203, noS8R113_Law2254, noS8R113_Law2264, noS8R113_Law2267, noS8R113_Law2270, noS8R113_Law2457, noS8R113_Law3053, noS8R113_Law3056, noS8R113_Law3066, noS8R113_Law3079, noS8R113_Law3083, noS8R113_Law3094, noS8R113_Law3518, noS8R113_Law3526, noS8R113_Law3549, noS8R113_Law3917, noS8R113_Law3962, noS8R113_Law4023, noS8R113_Law4275, noS8R113_Law4307, noS8R113_Law4585, noS8R113_Law4656⟩

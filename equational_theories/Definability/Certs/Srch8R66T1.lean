import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 2 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 2,263 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1075 takes them (329 nodes). -/
def ordS8R66_Law1075 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R66_Law1075 : ∀ v : Magma.tup8R66,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1082 takes them (186 nodes). -/
def ordS8R66_Law1082 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1082. -/
theorem noS8R66_Law1082 : ∀ v : Magma.tup8R66,
    ¬ @Equation1082 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1082) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1082) (by native_decide) v.1 v.2
    ((@Law1082.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (441 nodes). -/
def ordS8R66_Law1109 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1109. -/
theorem noS8R66_Law1109 : ∀ v : Magma.tup8R66,
    ¬ @Equation1109 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (266 nodes). -/
def ordS8R66_Law1122 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1122. -/
theorem noS8R66_Law1122 : ∀ v : Magma.tup8R66,
    ¬ @Equation1122 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (198 nodes). -/
def ordS8R66_Law1184 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1184. -/
theorem noS8R66_Law1184 : ∀ v : Magma.tup8R66,
    ¬ @Equation1184 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (385 nodes). -/
def ordS8R66_Law1278 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1278. -/
theorem noS8R66_Law1278 : ∀ v : Magma.tup8R66,
    ¬ @Equation1278 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (108 nodes). -/
def ordS8R66_Law1312 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1312. -/
theorem noS8R66_Law1312 : ∀ v : Magma.tup8R66,
    ¬ @Equation1312 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (216 nodes). -/
def ordS8R66_Law1325 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1325. -/
theorem noS8R66_Law1325 : ∀ v : Magma.tup8R66,
    ¬ @Equation1325 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1387 takes them (134 nodes). -/
def ordS8R66_Law1387 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1387. -/
theorem noS8R66_Law1387 : ∀ v : Magma.tup8R66,
    ¬ @Equation1387 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1387) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1387) (by native_decide) v.1 v.2
    ((@Law1387.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R66_refutes_1 :
    FamilyRefutes Magma.srch8R66 [
      1075, 1082, 1109, 1122, 1184, 1278, 1312, 1325, 1387
    ] :=
  ⟨noS8R66_Law1075, noS8R66_Law1082, noS8R66_Law1109, noS8R66_Law1122, noS8R66_Law1184, noS8R66_Law1278, noS8R66_Law1312, noS8R66_Law1325, noS8R66_Law1387⟩

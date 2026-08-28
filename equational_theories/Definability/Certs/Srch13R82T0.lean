import equational_theories.Definability.Srch_S13R82

/-!
# Structural certificate targets: `Magma.srch13R82`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S13R82_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `55` equations here, 168 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S13R82_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 124 takes them (3 nodes). -/
def ordS13R82_Law124 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 124. -/
theorem noS13R82_Law124 : ∀ v : Magma.tup13R82,
    ¬ @Equation124 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law124) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law124) (by native_decide) v.1 v.2
    ((@Law124.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 206 takes them (3 nodes). -/
def ordS13R82_Law206 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 206. -/
theorem noS13R82_Law206 : ∀ v : Magma.tup13R82,
    ¬ @Equation206 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law206) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law206) (by native_decide) v.1 v.2
    ((@Law206.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 427 takes them (3 nodes). -/
def ordS13R82_Law427 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 427. -/
theorem noS13R82_Law427 : ∀ v : Magma.tup13R82,
    ¬ @Equation427 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 437 takes them (3 nodes). -/
def ordS13R82_Law437 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 437. -/
theorem noS13R82_Law437 : ∀ v : Magma.tup13R82,
    ¬ @Equation437 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law437) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law437) (by native_decide) v.1 v.2
    ((@Law437.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 633 takes them (3 nodes). -/
def ordS13R82_Law633 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 633. -/
theorem noS13R82_Law633 : ∀ v : Magma.tup13R82,
    ¬ @Equation633 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law633) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law633) (by native_decide) v.1 v.2
    ((@Law633.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 639 takes them (4 nodes). -/
def ordS13R82_Law639 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 639. -/
theorem noS13R82_Law639 : ∀ v : Magma.tup13R82,
    ¬ @Equation639 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law639) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law639) (by native_decide) v.1 v.2
    ((@Law639.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 640 takes them (3 nodes). -/
def ordS13R82_Law640 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 640. -/
theorem noS13R82_Law640 : ∀ v : Magma.tup13R82,
    ¬ @Equation640 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law640) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law640) (by native_decide) v.1 v.2
    ((@Law640.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 882 takes them (3 nodes). -/
def ordS13R82_Law882 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 882. -/
theorem noS13R82_Law882 : ∀ v : Magma.tup13R82,
    ¬ @Equation882 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law882) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law882) (by native_decide) v.1 v.2
    ((@Law882.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 906 takes them (3 nodes). -/
def ordS13R82_Law906 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 906. -/
theorem noS13R82_Law906 : ∀ v : Magma.tup13R82,
    ¬ @Equation906 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law906) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law906) (by native_decide) v.1 v.2
    ((@Law906.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (3 nodes). -/
def ordS13R82_Law1023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1023. -/
theorem noS13R82_Law1023 : ∀ v : Magma.tup13R82,
    ¬ @Equation1023 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1039 takes them (3 nodes). -/
def ordS13R82_Law1039 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1039. -/
theorem noS13R82_Law1039 : ∀ v : Magma.tup13R82,
    ¬ @Equation1039 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (3 nodes). -/
def ordS13R82_Law1046 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1046. -/
theorem noS13R82_Law1046 : ∀ v : Magma.tup13R82,
    ¬ @Equation1046 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (3 nodes). -/
def ordS13R82_Law1109 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1109. -/
theorem noS13R82_Law1109 : ∀ v : Magma.tup13R82,
    ¬ @Equation1109 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1119 takes them (3 nodes). -/
def ordS13R82_Law1119 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1119. -/
theorem noS13R82_Law1119 : ∀ v : Magma.tup13R82,
    ¬ @Equation1119 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1119) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1119) (by native_decide) v.1 v.2
    ((@Law1119.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1171 takes them (3 nodes). -/
def ordS13R82_Law1171 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1171. -/
theorem noS13R82_Law1171 : ∀ v : Magma.tup13R82,
    ¬ @Equation1171 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1171) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1171) (by native_decide) v.1 v.2
    ((@Law1171.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (3 nodes). -/
def ordS13R82_Law1239 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1239. -/
theorem noS13R82_Law1239 : ∀ v : Magma.tup13R82,
    ¬ @Equation1239 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (3 nodes). -/
def ordS13R82_Law1242 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1242. -/
theorem noS13R82_Law1242 : ∀ v : Magma.tup13R82,
    ¬ @Equation1242 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1322 takes them (3 nodes). -/
def ordS13R82_Law1322 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1322. -/
theorem noS13R82_Law1322 : ∀ v : Magma.tup13R82,
    ¬ @Equation1322 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1322) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1322) (by native_decide) v.1 v.2
    ((@Law1322.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1340 takes them (3 nodes). -/
def ordS13R82_Law1340 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1340. -/
theorem noS13R82_Law1340 : ∀ v : Magma.tup13R82,
    ¬ @Equation1340 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1340) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1340) (by native_decide) v.1 v.2
    ((@Law1340.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (3 nodes). -/
def ordS13R82_Law1374 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1374. -/
theorem noS13R82_Law1374 : ∀ v : Magma.tup13R82,
    ¬ @Equation1374 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (3 nodes). -/
def ordS13R82_Law1467 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1467. -/
theorem noS13R82_Law1467 : ∀ v : Magma.tup13R82,
    ¬ @Equation1467 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1470 takes them (3 nodes). -/
def ordS13R82_Law1470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1470. -/
theorem noS13R82_Law1470 : ∀ v : Magma.tup13R82,
    ¬ @Equation1470 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1470) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1470) (by native_decide) v.1 v.2
    ((@Law1470.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1648 takes them (3 nodes). -/
def ordS13R82_Law1648 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1648. -/
theorem noS13R82_Law1648 : ∀ v : Magma.tup13R82,
    ¬ @Equation1648 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1648) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1648) (by native_decide) v.1 v.2
    ((@Law1648.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1670 takes them (3 nodes). -/
def ordS13R82_Law1670 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1670. -/
theorem noS13R82_Law1670 : ∀ v : Magma.tup13R82,
    ¬ @Equation1670 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1670) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1670) (by native_decide) v.1 v.2
    ((@Law1670.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1728 takes them (3 nodes). -/
def ordS13R82_Law1728 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1728. -/
theorem noS13R82_Law1728 : ∀ v : Magma.tup13R82,
    ¬ @Equation1728 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1728) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1728) (by native_decide) v.1 v.2
    ((@Law1728.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1793 takes them (3 nodes). -/
def ordS13R82_Law1793 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1793. -/
theorem noS13R82_Law1793 : ∀ v : Magma.tup13R82,
    ¬ @Equation1793 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1793) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1793) (by native_decide) v.1 v.2
    ((@Law1793.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1841 takes them (3 nodes). -/
def ordS13R82_Law1841 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1841. -/
theorem noS13R82_Law1841 : ∀ v : Magma.tup13R82,
    ¬ @Equation1841 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1841) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1841) (by native_decide) v.1 v.2
    ((@Law1841.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1876 takes them (3 nodes). -/
def ordS13R82_Law1876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1876. -/
theorem noS13R82_Law1876 : ∀ v : Magma.tup13R82,
    ¬ @Equation1876 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1876) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1876) (by native_decide) v.1 v.2
    ((@Law1876.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1924 takes them (3 nodes). -/
def ordS13R82_Law1924 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1924. -/
theorem noS13R82_Law1924 : ∀ v : Magma.tup13R82,
    ¬ @Equation1924 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1924) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law1924) (by native_decide) v.1 v.2
    ((@Law1924.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1983 takes them (3 nodes). -/
def ordS13R82_Law1983 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1983. -/
theorem noS13R82_Law1983 : ∀ v : Magma.tup13R82,
    ¬ @Equation1983 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1983) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law1983) (by native_decide) v.1 v.2
    ((@Law1983.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (3 nodes). -/
def ordS13R82_Law2186 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2186. -/
theorem noS13R82_Law2186 : ∀ v : Magma.tup13R82,
    ¬ @Equation2186 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (3 nodes). -/
def ordS13R82_Law2199 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2199. -/
theorem noS13R82_Law2199 : ∀ v : Magma.tup13R82,
    ¬ @Equation2199 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2247 takes them (3 nodes). -/
def ordS13R82_Law2247 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2247. -/
theorem noS13R82_Law2247 : ∀ v : Magma.tup13R82,
    ¬ @Equation2247 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2247) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2247) (by native_decide) v.1 v.2
    ((@Law2247.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2271 takes them (3 nodes). -/
def ordS13R82_Law2271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2271. -/
theorem noS13R82_Law2271 : ∀ v : Magma.tup13R82,
    ¬ @Equation2271 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2271) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law2271) (by native_decide) v.1 v.2
    ((@Law2271.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (3 nodes). -/
def ordS13R82_Law2279 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2279. -/
theorem noS13R82_Law2279 : ∀ v : Magma.tup13R82,
    ¬ @Equation2279 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (3 nodes). -/
def ordS13R82_Law2293 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2293. -/
theorem noS13R82_Law2293 : ∀ v : Magma.tup13R82,
    ¬ @Equation2293 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (3 nodes). -/
def ordS13R82_Law2330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2330. -/
theorem noS13R82_Law2330 : ∀ v : Magma.tup13R82,
    ¬ @Equation2330 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (3 nodes). -/
def ordS13R82_Law2444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2444. -/
theorem noS13R82_Law2444 : ∀ v : Magma.tup13R82,
    ¬ @Equation2444 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2450 takes them (3 nodes). -/
def ordS13R82_Law2450 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2450. -/
theorem noS13R82_Law2450 : ∀ v : Magma.tup13R82,
    ¬ @Equation2450 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2450) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2450) (by native_decide) v.1 v.2
    ((@Law2450.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2482 takes them (3 nodes). -/
def ordS13R82_Law2482 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2482. -/
theorem noS13R82_Law2482 : ∀ v : Magma.tup13R82,
    ¬ @Equation2482 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2482) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 3)
    (ord := ordS13R82_Law2482) (by native_decide) v.1 v.2
    ((@Law2482.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (3 nodes). -/
def ordS13R82_Law2506 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2506. -/
theorem noS13R82_Law2506 : ∀ v : Magma.tup13R82,
    ¬ @Equation2506 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (3 nodes). -/
def ordS13R82_Law2530 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2530. -/
theorem noS13R82_Law2530 : ∀ v : Magma.tup13R82,
    ¬ @Equation2530 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2533 takes them (3 nodes). -/
def ordS13R82_Law2533 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2533. -/
theorem noS13R82_Law2533 : ∀ v : Magma.tup13R82,
    ¬ @Equation2533 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2533) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2533) (by native_decide) v.1 v.2
    ((@Law2533.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2647 takes them (3 nodes). -/
def ordS13R82_Law2647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2647. -/
theorem noS13R82_Law2647 : ∀ v : Magma.tup13R82,
    ¬ @Equation2647 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2670 takes them (3 nodes). -/
def ordS13R82_Law2670 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2670. -/
theorem noS13R82_Law2670 : ∀ v : Magma.tup13R82,
    ¬ @Equation2670 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2670) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2670) (by native_decide) v.1 v.2
    ((@Law2670.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2855 takes them (4 nodes). -/
def ordS13R82_Law2855 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2855. -/
theorem noS13R82_Law2855 : ∀ v : Magma.tup13R82,
    ¬ @Equation2855 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2912 takes them (3 nodes). -/
def ordS13R82_Law2912 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2912. -/
theorem noS13R82_Law2912 : ∀ v : Magma.tup13R82,
    ¬ @Equation2912 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2912) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2912) (by native_decide) v.1 v.2
    ((@Law2912.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2939 takes them (3 nodes). -/
def ordS13R82_Law2939 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2939. -/
theorem noS13R82_Law2939 : ∀ v : Magma.tup13R82,
    ¬ @Equation2939 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2939) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law2939) (by native_decide) v.1 v.2
    ((@Law2939.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (3 nodes). -/
def ordS13R82_Law3105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3105. -/
theorem noS13R82_Law3105 : ∀ v : Magma.tup13R82,
    ¬ @Equation3105 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3115 takes them (3 nodes). -/
def ordS13R82_Law3115 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3115. -/
theorem noS13R82_Law3115 : ∀ v : Magma.tup13R82,
    ¬ @Equation3115 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3115) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law3115) (by native_decide) v.1 v.2
    ((@Law3115.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (3 nodes). -/
def ordS13R82_Law3343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3343. -/
theorem noS13R82_Law3343 : ∀ v : Magma.tup13R82,
    ¬ @Equation3343 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (3 nodes). -/
def ordS13R82_Law3481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3481. -/
theorem noS13R82_Law3481 : ∀ v : Magma.tup13R82,
    ¬ @Equation3481 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3865 takes them (3 nodes). -/
def ordS13R82_Law3865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3865. -/
theorem noS13R82_Law3865 : ∀ v : Magma.tup13R82,
    ¬ @Equation3865 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (3 nodes). -/
def ordS13R82_Law4130 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4130. -/
theorem noS13R82_Law4130 : ∀ v : Magma.tup13R82,
    ¬ @Equation4130 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4399 takes them (4 nodes). -/
def ordS13R82_Law4399 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4399. -/
theorem noS13R82_Law4399 : ∀ v : Magma.tup13R82,
    ¬ @Equation4399 (Fin 13) (Magma.srch13R82 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4399) (E := S13R82.E) (tr := S13R82.tr) (z := S13R82.z)
    (st := S13R82.st) (X := S13R82.X) (envs := Magma.envsRed 13 S13R82.E 2)
    (ord := ordS13R82_Law4399) (by native_decide) v.1 v.2
    ((@Law4399.models_iff (Fin 13) (Magma.srch13R82 v)).mpr hv)

/-- No member of the class satisfies any of these `55` equations. -/
theorem srch13R82_refutes_0 :
    FamilyRefutes Magma.srch13R82 [
      124, 206, 427, 437, 633, 639, 640, 882, 906, 1023, 1039, 1046, 1109, 1119, 1171, 1239,
      1242, 1322, 1340, 1374, 1467, 1470, 1648, 1670, 1728, 1793, 1841, 1876, 1924, 1983, 2186,
      2199, 2247, 2271, 2279, 2293, 2330, 2444, 2450, 2482, 2506, 2530, 2533, 2647, 2670, 2855,
      2912, 2939, 3105, 3115, 3343, 3481, 3865, 4130, 4399
    ] :=
  ⟨noS13R82_Law124, noS13R82_Law206, noS13R82_Law427, noS13R82_Law437, noS13R82_Law633, noS13R82_Law639, noS13R82_Law640, noS13R82_Law882, noS13R82_Law906, noS13R82_Law1023, noS13R82_Law1039, noS13R82_Law1046, noS13R82_Law1109, noS13R82_Law1119, noS13R82_Law1171, noS13R82_Law1239, noS13R82_Law1242, noS13R82_Law1322, noS13R82_Law1340, noS13R82_Law1374, noS13R82_Law1467, noS13R82_Law1470, noS13R82_Law1648, noS13R82_Law1670, noS13R82_Law1728, noS13R82_Law1793, noS13R82_Law1841, noS13R82_Law1876, noS13R82_Law1924, noS13R82_Law1983, noS13R82_Law2186, noS13R82_Law2199, noS13R82_Law2247, noS13R82_Law2271, noS13R82_Law2279, noS13R82_Law2293, noS13R82_Law2330, noS13R82_Law2444, noS13R82_Law2450, noS13R82_Law2482, noS13R82_Law2506, noS13R82_Law2530, noS13R82_Law2533, noS13R82_Law2647, noS13R82_Law2670, noS13R82_Law2855, noS13R82_Law2912, noS13R82_Law2939, noS13R82_Law3105, noS13R82_Law3115, noS13R82_Law3343, noS13R82_Law3481, noS13R82_Law3865, noS13R82_Law4130, noS13R82_Law4399⟩

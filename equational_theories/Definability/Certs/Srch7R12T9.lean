import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 10 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 3,410 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1060 takes them (203 nodes). -/
def ordS7R12_Law1060 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1060. -/
theorem noS7R12_Law1060 : ∀ v : Magma.tup7R12,
    ¬ @Equation1060 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1060) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1060) (by native_decide) v.1 v.2
    ((@Law1060.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1061 takes them (150 nodes). -/
def ordS7R12_Law1061 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1061. -/
theorem noS7R12_Law1061 : ∀ v : Magma.tup7R12,
    ¬ @Equation1061 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1061) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1061) (by native_decide) v.1 v.2
    ((@Law1061.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1067 takes them (211 nodes). -/
def ordS7R12_Law1067 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1067. -/
theorem noS7R12_Law1067 : ∀ v : Magma.tup7R12,
    ¬ @Equation1067 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1067) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1067) (by native_decide) v.1 v.2
    ((@Law1067.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1068 takes them (99 nodes). -/
def ordS7R12_Law1068 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1068. -/
theorem noS7R12_Law1068 : ∀ v : Magma.tup7R12,
    ¬ @Equation1068 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1068) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1068) (by native_decide) v.1 v.2
    ((@Law1068.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (510 nodes). -/
def ordS7R12_Law1075 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1075. -/
theorem noS7R12_Law1075 : ∀ v : Magma.tup7R12,
    ¬ @Equation1075 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (388 nodes). -/
def ordS7R12_Law1109 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1109. -/
theorem noS7R12_Law1109 : ∀ v : Magma.tup7R12,
    ¬ @Equation1109 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (558 nodes). -/
def ordS7R12_Law1122 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1122. -/
theorem noS7R12_Law1122 : ∀ v : Magma.tup7R12,
    ¬ @Equation1122 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (230 nodes). -/
def ordS7R12_Law1184 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1184. -/
theorem noS7R12_Law1184 : ∀ v : Magma.tup7R12,
    ¬ @Equation1184 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1230 takes them (221 nodes). -/
def ordS7R12_Law1230 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1230. -/
theorem noS7R12_Law1230 : ∀ v : Magma.tup7R12,
    ¬ @Equation1230 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1230) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1230) (by native_decide) v.1 v.2
    ((@Law1230.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1233 takes them (121 nodes). -/
def ordS7R12_Law1233 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1233. -/
theorem noS7R12_Law1233 : ∀ v : Magma.tup7R12,
    ¬ @Equation1233 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1233) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1233) (by native_decide) v.1 v.2
    ((@Law1233.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1234 takes them (438 nodes). -/
def ordS7R12_Law1234 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1234. -/
theorem noS7R12_Law1234 : ∀ v : Magma.tup7R12,
    ¬ @Equation1234 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1234) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1234) (by native_decide) v.1 v.2
    ((@Law1234.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1235 takes them (99 nodes). -/
def ordS7R12_Law1235 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1235. -/
theorem noS7R12_Law1235 : ∀ v : Magma.tup7R12,
    ¬ @Equation1235 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1235) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1235) (by native_decide) v.1 v.2
    ((@Law1235.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1236 takes them (111 nodes). -/
def ordS7R12_Law1236 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1236. -/
theorem noS7R12_Law1236 : ∀ v : Magma.tup7R12,
    ¬ @Equation1236 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1236) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1236) (by native_decide) v.1 v.2
    ((@Law1236.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1237 takes them (71 nodes). -/
def ordS7R12_Law1237 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1237. -/
theorem noS7R12_Law1237 : ∀ v : Magma.tup7R12,
    ¬ @Equation1237 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1237) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1237) (by native_decide) v.1 v.2
    ((@Law1237.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch7R12_refutes_9 :
    FamilyRefutes Magma.srch7R12 [
      1060, 1061, 1067, 1068, 1075, 1109, 1122, 1184, 1230, 1233, 1234, 1235, 1236, 1237
    ] :=
  ⟨noS7R12_Law1060, noS7R12_Law1061, noS7R12_Law1067, noS7R12_Law1068, noS7R12_Law1075, noS7R12_Law1109, noS7R12_Law1122, noS7R12_Law1184, noS7R12_Law1230, noS7R12_Law1233, noS7R12_Law1234, noS7R12_Law1235, noS7R12_Law1236, noS7R12_Law1237⟩

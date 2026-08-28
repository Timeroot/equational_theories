import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 3 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 318 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1025 takes them (4 nodes). -/
def ordS11R173_Law1025 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1025. -/
theorem noS11R173_Law1025 : ∀ v : Magma.tup11R173,
    ¬ @Equation1025 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1026 takes them (3 nodes). -/
def ordS11R173_Law1026 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1026. -/
theorem noS11R173_Law1026 : ∀ v : Magma.tup11R173,
    ¬ @Equation1026 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1026) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1026) (by native_decide) v.1 v.2
    ((@Law1026.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1027 takes them (3 nodes). -/
def ordS11R173_Law1027 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1027. -/
theorem noS11R173_Law1027 : ∀ v : Magma.tup11R173,
    ¬ @Equation1027 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1027) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1027) (by native_decide) v.1 v.2
    ((@Law1027.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1028 takes them (4 nodes). -/
def ordS11R173_Law1028 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1028. -/
theorem noS11R173_Law1028 : ∀ v : Magma.tup11R173,
    ¬ @Equation1028 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1028) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1028) (by native_decide) v.1 v.2
    ((@Law1028.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1030 takes them (3 nodes). -/
def ordS11R173_Law1030 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1030. -/
theorem noS11R173_Law1030 : ∀ v : Magma.tup11R173,
    ¬ @Equation1030 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1030) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1030) (by native_decide) v.1 v.2
    ((@Law1030.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (4 nodes). -/
def ordS11R173_Law1031 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1031. -/
theorem noS11R173_Law1031 : ∀ v : Magma.tup11R173,
    ¬ @Equation1031 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1032 takes them (3 nodes). -/
def ordS11R173_Law1032 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1032. -/
theorem noS11R173_Law1032 : ∀ v : Magma.tup11R173,
    ¬ @Equation1032 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1032) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1032) (by native_decide) v.1 v.2
    ((@Law1032.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1033 takes them (3 nodes). -/
def ordS11R173_Law1033 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1033. -/
theorem noS11R173_Law1033 : ∀ v : Magma.tup11R173,
    ¬ @Equation1033 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1033) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1033) (by native_decide) v.1 v.2
    ((@Law1033.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1034 takes them (3 nodes). -/
def ordS11R173_Law1034 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1034. -/
theorem noS11R173_Law1034 : ∀ v : Magma.tup11R173,
    ¬ @Equation1034 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1034) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law1034) (by native_decide) v.1 v.2
    ((@Law1034.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1035 takes them (4 nodes). -/
def ordS11R173_Law1035 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1035. -/
theorem noS11R173_Law1035 : ∀ v : Magma.tup11R173,
    ¬ @Equation1035 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1035) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1035) (by native_decide) v.1 v.2
    ((@Law1035.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (3 nodes). -/
def ordS11R173_Law1036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1036. -/
theorem noS11R173_Law1036 : ∀ v : Magma.tup11R173,
    ¬ @Equation1036 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1038 takes them (4 nodes). -/
def ordS11R173_Law1038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1038. -/
theorem noS11R173_Law1038 : ∀ v : Magma.tup11R173,
    ¬ @Equation1038 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1038) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1038) (by native_decide) v.1 v.2
    ((@Law1038.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1041 takes them (4 nodes). -/
def ordS11R173_Law1041 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1041. -/
theorem noS11R173_Law1041 : ∀ v : Magma.tup11R173,
    ¬ @Equation1041 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1041) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1041) (by native_decide) v.1 v.2
    ((@Law1041.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1048 takes them (4 nodes). -/
def ordS11R173_Law1048 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1048. -/
theorem noS11R173_Law1048 : ∀ v : Magma.tup11R173,
    ¬ @Equation1048 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1048) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1048) (by native_decide) v.1 v.2
    ((@Law1048.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1051 takes them (4 nodes). -/
def ordS11R173_Law1051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1051. -/
theorem noS11R173_Law1051 : ∀ v : Magma.tup11R173,
    ¬ @Equation1051 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1051) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1051) (by native_decide) v.1 v.2
    ((@Law1051.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1055 takes them (4 nodes). -/
def ordS11R173_Law1055 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1055. -/
theorem noS11R173_Law1055 : ∀ v : Magma.tup11R173,
    ¬ @Equation1055 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1055) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1055) (by native_decide) v.1 v.2
    ((@Law1055.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1059 takes them (4 nodes). -/
def ordS11R173_Law1059 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1059. -/
theorem noS11R173_Law1059 : ∀ v : Magma.tup11R173,
    ¬ @Equation1059 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1059) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1059) (by native_decide) v.1 v.2
    ((@Law1059.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1063 takes them (4 nodes). -/
def ordS11R173_Law1063 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1063. -/
theorem noS11R173_Law1063 : ∀ v : Magma.tup11R173,
    ¬ @Equation1063 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1063) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1063) (by native_decide) v.1 v.2
    ((@Law1063.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1067 takes them (4 nodes). -/
def ordS11R173_Law1067 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1067. -/
theorem noS11R173_Law1067 : ∀ v : Magma.tup11R173,
    ¬ @Equation1067 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1067) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law1067) (by native_decide) v.1 v.2
    ((@Law1067.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1085 takes them (3 nodes). -/
def ordS11R173_Law1085 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1085. -/
theorem noS11R173_Law1085 : ∀ v : Magma.tup11R173,
    ¬ @Equation1085 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1085) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1085) (by native_decide) v.1 v.2
    ((@Law1085.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1224 takes them (3 nodes). -/
def ordS11R173_Law1224 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1224. -/
theorem noS11R173_Law1224 : ∀ v : Magma.tup11R173,
    ¬ @Equation1224 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1224) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1224) (by native_decide) v.1 v.2
    ((@Law1224.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1225 takes them (4 nodes). -/
def ordS11R173_Law1225 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1225. -/
theorem noS11R173_Law1225 : ∀ v : Magma.tup11R173,
    ¬ @Equation1225 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1225) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1225) (by native_decide) v.1 v.2
    ((@Law1225.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1227 takes them (3 nodes). -/
def ordS11R173_Law1227 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1227. -/
theorem noS11R173_Law1227 : ∀ v : Magma.tup11R173,
    ¬ @Equation1227 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1227) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1227) (by native_decide) v.1 v.2
    ((@Law1227.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1228 takes them (4 nodes). -/
def ordS11R173_Law1228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1228. -/
theorem noS11R173_Law1228 : ∀ v : Magma.tup11R173,
    ¬ @Equation1228 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1228) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1228) (by native_decide) v.1 v.2
    ((@Law1228.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (3 nodes). -/
def ordS11R173_Law1229 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1229. -/
theorem noS11R173_Law1229 : ∀ v : Magma.tup11R173,
    ¬ @Equation1229 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1230 takes them (3 nodes). -/
def ordS11R173_Law1230 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1230. -/
theorem noS11R173_Law1230 : ∀ v : Magma.tup11R173,
    ¬ @Equation1230 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1230) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1230) (by native_decide) v.1 v.2
    ((@Law1230.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1232 takes them (3 nodes). -/
def ordS11R173_Law1232 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1232. -/
theorem noS11R173_Law1232 : ∀ v : Magma.tup11R173,
    ¬ @Equation1232 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1232) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1232) (by native_decide) v.1 v.2
    ((@Law1232.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1233 takes them (3 nodes). -/
def ordS11R173_Law1233 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1233. -/
theorem noS11R173_Law1233 : ∀ v : Magma.tup11R173,
    ¬ @Equation1233 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1233) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1233) (by native_decide) v.1 v.2
    ((@Law1233.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1234 takes them (4 nodes). -/
def ordS11R173_Law1234 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1234. -/
theorem noS11R173_Law1234 : ∀ v : Magma.tup11R173,
    ¬ @Equation1234 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1234) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1234) (by native_decide) v.1 v.2
    ((@Law1234.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1235 takes them (3 nodes). -/
def ordS11R173_Law1235 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1235. -/
theorem noS11R173_Law1235 : ∀ v : Magma.tup11R173,
    ¬ @Equation1235 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1235) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1235) (by native_decide) v.1 v.2
    ((@Law1235.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1236 takes them (3 nodes). -/
def ordS11R173_Law1236 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1236. -/
theorem noS11R173_Law1236 : ∀ v : Magma.tup11R173,
    ¬ @Equation1236 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1236) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1236) (by native_decide) v.1 v.2
    ((@Law1236.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1237 takes them (3 nodes). -/
def ordS11R173_Law1237 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1237. -/
theorem noS11R173_Law1237 : ∀ v : Magma.tup11R173,
    ¬ @Equation1237 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1237) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law1237) (by native_decide) v.1 v.2
    ((@Law1237.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1238 takes them (4 nodes). -/
def ordS11R173_Law1238 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1238. -/
theorem noS11R173_Law1238 : ∀ v : Magma.tup11R173,
    ¬ @Equation1238 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1238) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1238) (by native_decide) v.1 v.2
    ((@Law1238.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1241 takes them (4 nodes). -/
def ordS11R173_Law1241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1241. -/
theorem noS11R173_Law1241 : ∀ v : Magma.tup11R173,
    ¬ @Equation1241 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1241) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1241) (by native_decide) v.1 v.2
    ((@Law1241.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1244 takes them (4 nodes). -/
def ordS11R173_Law1244 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1244. -/
theorem noS11R173_Law1244 : ∀ v : Magma.tup11R173,
    ¬ @Equation1244 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1244) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1244) (by native_decide) v.1 v.2
    ((@Law1244.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1248 takes them (4 nodes). -/
def ordS11R173_Law1248 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1248. -/
theorem noS11R173_Law1248 : ∀ v : Magma.tup11R173,
    ¬ @Equation1248 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1248) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1248) (by native_decide) v.1 v.2
    ((@Law1248.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (3 nodes). -/
def ordS11R173_Law1249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1249. -/
theorem noS11R173_Law1249 : ∀ v : Magma.tup11R173,
    ¬ @Equation1249 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1251 takes them (4 nodes). -/
def ordS11R173_Law1251 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1251. -/
theorem noS11R173_Law1251 : ∀ v : Magma.tup11R173,
    ¬ @Equation1251 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1251) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1251) (by native_decide) v.1 v.2
    ((@Law1251.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1254 takes them (4 nodes). -/
def ordS11R173_Law1254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1254. -/
theorem noS11R173_Law1254 : ∀ v : Magma.tup11R173,
    ¬ @Equation1254 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1254) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1254) (by native_decide) v.1 v.2
    ((@Law1254.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1258 takes them (4 nodes). -/
def ordS11R173_Law1258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1258. -/
theorem noS11R173_Law1258 : ∀ v : Magma.tup11R173,
    ¬ @Equation1258 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1258) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1258) (by native_decide) v.1 v.2
    ((@Law1258.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1259 takes them (3 nodes). -/
def ordS11R173_Law1259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1259. -/
theorem noS11R173_Law1259 : ∀ v : Magma.tup11R173,
    ¬ @Equation1259 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1259) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1259) (by native_decide) v.1 v.2
    ((@Law1259.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1260 takes them (3 nodes). -/
def ordS11R173_Law1260 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1260. -/
theorem noS11R173_Law1260 : ∀ v : Magma.tup11R173,
    ¬ @Equation1260 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1260) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1260) (by native_decide) v.1 v.2
    ((@Law1260.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1262 takes them (4 nodes). -/
def ordS11R173_Law1262 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1262. -/
theorem noS11R173_Law1262 : ∀ v : Magma.tup11R173,
    ¬ @Equation1262 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1262) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1262) (by native_decide) v.1 v.2
    ((@Law1262.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1266 takes them (4 nodes). -/
def ordS11R173_Law1266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1266. -/
theorem noS11R173_Law1266 : ∀ v : Magma.tup11R173,
    ¬ @Equation1266 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1266) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1266) (by native_decide) v.1 v.2
    ((@Law1266.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1270 takes them (4 nodes). -/
def ordS11R173_Law1270 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1270. -/
theorem noS11R173_Law1270 : ∀ v : Magma.tup11R173,
    ¬ @Equation1270 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1270) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law1270) (by native_decide) v.1 v.2
    ((@Law1270.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (3 nodes). -/
def ordS11R173_Law1278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1278. -/
theorem noS11R173_Law1278 : ∀ v : Magma.tup11R173,
    ¬ @Equation1278 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1427 takes them (3 nodes). -/
def ordS11R173_Law1427 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1427. -/
theorem noS11R173_Law1427 : ∀ v : Magma.tup11R173,
    ¬ @Equation1427 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1427) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1427) (by native_decide) v.1 v.2
    ((@Law1427.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1428 takes them (4 nodes). -/
def ordS11R173_Law1428 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1428. -/
theorem noS11R173_Law1428 : ∀ v : Magma.tup11R173,
    ¬ @Equation1428 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1428) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1428) (by native_decide) v.1 v.2
    ((@Law1428.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1429 takes them (3 nodes). -/
def ordS11R173_Law1429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1429. -/
theorem noS11R173_Law1429 : ∀ v : Magma.tup11R173,
    ¬ @Equation1429 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1429) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1429) (by native_decide) v.1 v.2
    ((@Law1429.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1430 takes them (3 nodes). -/
def ordS11R173_Law1430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1430. -/
theorem noS11R173_Law1430 : ∀ v : Magma.tup11R173,
    ¬ @Equation1430 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1430) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1430) (by native_decide) v.1 v.2
    ((@Law1430.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1431 takes them (4 nodes). -/
def ordS11R173_Law1431 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1431. -/
theorem noS11R173_Law1431 : ∀ v : Magma.tup11R173,
    ¬ @Equation1431 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1431) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1431) (by native_decide) v.1 v.2
    ((@Law1431.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1437 takes them (4 nodes). -/
def ordS11R173_Law1437 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1437. -/
theorem noS11R173_Law1437 : ∀ v : Magma.tup11R173,
    ¬ @Equation1437 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1437) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1437) (by native_decide) v.1 v.2
    ((@Law1437.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1441 takes them (4 nodes). -/
def ordS11R173_Law1441 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1441. -/
theorem noS11R173_Law1441 : ∀ v : Magma.tup11R173,
    ¬ @Equation1441 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1441) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1441) (by native_decide) v.1 v.2
    ((@Law1441.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (3 nodes). -/
def ordS11R173_Law1442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1442. -/
theorem noS11R173_Law1442 : ∀ v : Magma.tup11R173,
    ¬ @Equation1442 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1443 takes them (3 nodes). -/
def ordS11R173_Law1443 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1443. -/
theorem noS11R173_Law1443 : ∀ v : Magma.tup11R173,
    ¬ @Equation1443 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1443) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1443) (by native_decide) v.1 v.2
    ((@Law1443.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1447 takes them (4 nodes). -/
def ordS11R173_Law1447 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1447. -/
theorem noS11R173_Law1447 : ∀ v : Magma.tup11R173,
    ¬ @Equation1447 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1447) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1447) (by native_decide) v.1 v.2
    ((@Law1447.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1451 takes them (4 nodes). -/
def ordS11R173_Law1451 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1451. -/
theorem noS11R173_Law1451 : ∀ v : Magma.tup11R173,
    ¬ @Equation1451 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1451) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1451) (by native_decide) v.1 v.2
    ((@Law1451.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1452 takes them (3 nodes). -/
def ordS11R173_Law1452 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1452. -/
theorem noS11R173_Law1452 : ∀ v : Magma.tup11R173,
    ¬ @Equation1452 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1452) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1452) (by native_decide) v.1 v.2
    ((@Law1452.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1478 takes them (3 nodes). -/
def ordS11R173_Law1478 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1478. -/
theorem noS11R173_Law1478 : ∀ v : Magma.tup11R173,
    ¬ @Equation1478 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1478) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1478) (by native_decide) v.1 v.2
    ((@Law1478.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (3 nodes). -/
def ordS11R173_Law1481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1481. -/
theorem noS11R173_Law1481 : ∀ v : Magma.tup11R173,
    ¬ @Equation1481 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1491 takes them (3 nodes). -/
def ordS11R173_Law1491 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1491. -/
theorem noS11R173_Law1491 : ∀ v : Magma.tup11R173,
    ¬ @Equation1491 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1491) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1491) (by native_decide) v.1 v.2
    ((@Law1491.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1518 takes them (3 nodes). -/
def ordS11R173_Law1518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1518. -/
theorem noS11R173_Law1518 : ∀ v : Magma.tup11R173,
    ¬ @Equation1518 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1518) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1518) (by native_decide) v.1 v.2
    ((@Law1518.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (3 nodes). -/
def ordS11R173_Law1528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1528. -/
theorem noS11R173_Law1528 : ∀ v : Magma.tup11R173,
    ¬ @Equation1528 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1630 takes them (3 nodes). -/
def ordS11R173_Law1630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1630. -/
theorem noS11R173_Law1630 : ∀ v : Magma.tup11R173,
    ¬ @Equation1630 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1630) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1630) (by native_decide) v.1 v.2
    ((@Law1630.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1631 takes them (4 nodes). -/
def ordS11R173_Law1631 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1631. -/
theorem noS11R173_Law1631 : ∀ v : Magma.tup11R173,
    ¬ @Equation1631 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1631) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1631) (by native_decide) v.1 v.2
    ((@Law1631.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1633 takes them (3 nodes). -/
def ordS11R173_Law1633 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1633. -/
theorem noS11R173_Law1633 : ∀ v : Magma.tup11R173,
    ¬ @Equation1633 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1633) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1633) (by native_decide) v.1 v.2
    ((@Law1633.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1634 takes them (4 nodes). -/
def ordS11R173_Law1634 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1634. -/
theorem noS11R173_Law1634 : ∀ v : Magma.tup11R173,
    ¬ @Equation1634 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1634) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1634) (by native_decide) v.1 v.2
    ((@Law1634.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (3 nodes). -/
def ordS11R173_Law1635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1635. -/
theorem noS11R173_Law1635 : ∀ v : Magma.tup11R173,
    ¬ @Equation1635 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1637 takes them (4 nodes). -/
def ordS11R173_Law1637 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1637. -/
theorem noS11R173_Law1637 : ∀ v : Magma.tup11R173,
    ¬ @Equation1637 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1637) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1637) (by native_decide) v.1 v.2
    ((@Law1637.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1640 takes them (4 nodes). -/
def ordS11R173_Law1640 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1640. -/
theorem noS11R173_Law1640 : ∀ v : Magma.tup11R173,
    ¬ @Equation1640 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1640) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1640) (by native_decide) v.1 v.2
    ((@Law1640.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1644 takes them (4 nodes). -/
def ordS11R173_Law1644 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1644. -/
theorem noS11R173_Law1644 : ∀ v : Magma.tup11R173,
    ¬ @Equation1644 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1644) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1644) (by native_decide) v.1 v.2
    ((@Law1644.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1650 takes them (4 nodes). -/
def ordS11R173_Law1650 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1650. -/
theorem noS11R173_Law1650 : ∀ v : Magma.tup11R173,
    ¬ @Equation1650 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1650) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1650) (by native_decide) v.1 v.2
    ((@Law1650.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1655 takes them (3 nodes). -/
def ordS11R173_Law1655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1655. -/
theorem noS11R173_Law1655 : ∀ v : Magma.tup11R173,
    ¬ @Equation1655 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1655) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1655) (by native_decide) v.1 v.2
    ((@Law1655.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1657 takes them (4 nodes). -/
def ordS11R173_Law1657 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1657. -/
theorem noS11R173_Law1657 : ∀ v : Magma.tup11R173,
    ¬ @Equation1657 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1664 takes them (4 nodes). -/
def ordS11R173_Law1664 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1664. -/
theorem noS11R173_Law1664 : ∀ v : Magma.tup11R173,
    ¬ @Equation1664 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1664) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1664) (by native_decide) v.1 v.2
    ((@Law1664.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1681 takes them (3 nodes). -/
def ordS11R173_Law1681 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1681. -/
theorem noS11R173_Law1681 : ∀ v : Magma.tup11R173,
    ¬ @Equation1681 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1681) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1681) (by native_decide) v.1 v.2
    ((@Law1681.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (3 nodes). -/
def ordS11R173_Law1684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1684. -/
theorem noS11R173_Law1684 : ∀ v : Magma.tup11R173,
    ¬ @Equation1684 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1687 takes them (3 nodes). -/
def ordS11R173_Law1687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1687. -/
theorem noS11R173_Law1687 : ∀ v : Magma.tup11R173,
    ¬ @Equation1687 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1687) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1687) (by native_decide) v.1 v.2
    ((@Law1687.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1701 takes them (3 nodes). -/
def ordS11R173_Law1701 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1701. -/
theorem noS11R173_Law1701 : ∀ v : Magma.tup11R173,
    ¬ @Equation1701 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1701) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1701) (by native_decide) v.1 v.2
    ((@Law1701.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1721 takes them (3 nodes). -/
def ordS11R173_Law1721 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1721. -/
theorem noS11R173_Law1721 : ∀ v : Magma.tup11R173,
    ¬ @Equation1721 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1721) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1721) (by native_decide) v.1 v.2
    ((@Law1721.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1833 takes them (3 nodes). -/
def ordS11R173_Law1833 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1833. -/
theorem noS11R173_Law1833 : ∀ v : Magma.tup11R173,
    ¬ @Equation1833 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1833) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1833) (by native_decide) v.1 v.2
    ((@Law1833.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1834 takes them (4 nodes). -/
def ordS11R173_Law1834 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1834. -/
theorem noS11R173_Law1834 : ∀ v : Magma.tup11R173,
    ¬ @Equation1834 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1834) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1834) (by native_decide) v.1 v.2
    ((@Law1834.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1837 takes them (4 nodes). -/
def ordS11R173_Law1837 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1837. -/
theorem noS11R173_Law1837 : ∀ v : Magma.tup11R173,
    ¬ @Equation1837 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1837) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1837) (by native_decide) v.1 v.2
    ((@Law1837.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1839 takes them (3 nodes). -/
def ordS11R173_Law1839 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1839. -/
theorem noS11R173_Law1839 : ∀ v : Magma.tup11R173,
    ¬ @Equation1839 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1839) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1839) (by native_decide) v.1 v.2
    ((@Law1839.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1843 takes them (4 nodes). -/
def ordS11R173_Law1843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1843. -/
theorem noS11R173_Law1843 : ∀ v : Magma.tup11R173,
    ¬ @Equation1843 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1843) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1843) (by native_decide) v.1 v.2
    ((@Law1843.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1847 takes them (4 nodes). -/
def ordS11R173_Law1847 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1847. -/
theorem noS11R173_Law1847 : ∀ v : Magma.tup11R173,
    ¬ @Equation1847 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1847) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1847) (by native_decide) v.1 v.2
    ((@Law1847.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (3 nodes). -/
def ordS11R173_Law1848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1848. -/
theorem noS11R173_Law1848 : ∀ v : Magma.tup11R173,
    ¬ @Equation1848 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1849 takes them (3 nodes). -/
def ordS11R173_Law1849 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1849. -/
theorem noS11R173_Law1849 : ∀ v : Magma.tup11R173,
    ¬ @Equation1849 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1849) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1849) (by native_decide) v.1 v.2
    ((@Law1849.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1851 takes them (3 nodes). -/
def ordS11R173_Law1851 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1851. -/
theorem noS11R173_Law1851 : ∀ v : Magma.tup11R173,
    ¬ @Equation1851 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1851) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1851) (by native_decide) v.1 v.2
    ((@Law1851.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1853 takes them (4 nodes). -/
def ordS11R173_Law1853 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1853. -/
theorem noS11R173_Law1853 : ∀ v : Magma.tup11R173,
    ¬ @Equation1853 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1853) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1853) (by native_decide) v.1 v.2
    ((@Law1853.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1857 takes them (4 nodes). -/
def ordS11R173_Law1857 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1857. -/
theorem noS11R173_Law1857 : ∀ v : Magma.tup11R173,
    ¬ @Equation1857 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1857) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1857) (by native_decide) v.1 v.2
    ((@Law1857.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch11R173_refutes_2 :
    FamilyRefutes Magma.srch11R173 [
      1025, 1026, 1027, 1028, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1038, 1041, 1048, 1051,
      1055, 1059, 1063, 1067, 1085, 1224, 1225, 1227, 1228, 1229, 1230, 1232, 1233, 1234, 1235,
      1236, 1237, 1238, 1241, 1244, 1248, 1249, 1251, 1254, 1258, 1259, 1260, 1262, 1266, 1270,
      1278, 1427, 1428, 1429, 1430, 1431, 1437, 1441, 1442, 1443, 1447, 1451, 1452, 1478, 1481,
      1491, 1518, 1528, 1630, 1631, 1633, 1634, 1635, 1637, 1640, 1644, 1650, 1655, 1657, 1664,
      1681, 1684, 1687, 1701, 1721, 1833, 1834, 1837, 1839, 1843, 1847, 1848, 1849, 1851, 1853,
      1857
    ] :=
  ⟨noS11R173_Law1025, noS11R173_Law1026, noS11R173_Law1027, noS11R173_Law1028, noS11R173_Law1030, noS11R173_Law1031, noS11R173_Law1032, noS11R173_Law1033, noS11R173_Law1034, noS11R173_Law1035, noS11R173_Law1036, noS11R173_Law1038, noS11R173_Law1041, noS11R173_Law1048, noS11R173_Law1051, noS11R173_Law1055, noS11R173_Law1059, noS11R173_Law1063, noS11R173_Law1067, noS11R173_Law1085, noS11R173_Law1224, noS11R173_Law1225, noS11R173_Law1227, noS11R173_Law1228, noS11R173_Law1229, noS11R173_Law1230, noS11R173_Law1232, noS11R173_Law1233, noS11R173_Law1234, noS11R173_Law1235, noS11R173_Law1236, noS11R173_Law1237, noS11R173_Law1238, noS11R173_Law1241, noS11R173_Law1244, noS11R173_Law1248, noS11R173_Law1249, noS11R173_Law1251, noS11R173_Law1254, noS11R173_Law1258, noS11R173_Law1259, noS11R173_Law1260, noS11R173_Law1262, noS11R173_Law1266, noS11R173_Law1270, noS11R173_Law1278, noS11R173_Law1427, noS11R173_Law1428, noS11R173_Law1429, noS11R173_Law1430, noS11R173_Law1431, noS11R173_Law1437, noS11R173_Law1441, noS11R173_Law1442, noS11R173_Law1443, noS11R173_Law1447, noS11R173_Law1451, noS11R173_Law1452, noS11R173_Law1478, noS11R173_Law1481, noS11R173_Law1491, noS11R173_Law1518, noS11R173_Law1528, noS11R173_Law1630, noS11R173_Law1631, noS11R173_Law1633, noS11R173_Law1634, noS11R173_Law1635, noS11R173_Law1637, noS11R173_Law1640, noS11R173_Law1644, noS11R173_Law1650, noS11R173_Law1655, noS11R173_Law1657, noS11R173_Law1664, noS11R173_Law1681, noS11R173_Law1684, noS11R173_Law1687, noS11R173_Law1701, noS11R173_Law1721, noS11R173_Law1833, noS11R173_Law1834, noS11R173_Law1837, noS11R173_Law1839, noS11R173_Law1843, noS11R173_Law1847, noS11R173_Law1848, noS11R173_Law1849, noS11R173_Law1851, noS11R173_Law1853, noS11R173_Law1857⟩

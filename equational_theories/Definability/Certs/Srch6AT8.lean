import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 9 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `31`
equations here, 2,643 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 926 takes them (157 nodes). -/
def ordS6A_Law926 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 926. -/
theorem noS6A_Law926 : ∀ v : Magma.tupS6A,
    ¬ @Equation926 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law926) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law926) (by native_decide) v.1 v.2
    ((@Law926.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 930 takes them (46 nodes). -/
def ordS6A_Law930 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 930. -/
theorem noS6A_Law930 : ∀ v : Magma.tupS6A,
    ¬ @Equation930 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law930) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law930) (by native_decide) v.1 v.2
    ((@Law930.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 934 takes them (92 nodes). -/
def ordS6A_Law934 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 934. -/
theorem noS6A_Law934 : ∀ v : Magma.tupS6A,
    ¬ @Equation934 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law934) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law934) (by native_decide) v.1 v.2
    ((@Law934.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 938 takes them (37 nodes). -/
def ordS6A_Law938 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 938. -/
theorem noS6A_Law938 : ∀ v : Magma.tupS6A,
    ¬ @Equation938 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law938) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law938) (by native_decide) v.1 v.2
    ((@Law938.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 943 takes them (173 nodes). -/
def ordS6A_Law943 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 943. -/
theorem noS6A_Law943 : ∀ v : Magma.tupS6A,
    ¬ @Equation943 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law943) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law943) (by native_decide) v.1 v.2
    ((@Law943.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 947 takes them (61 nodes). -/
def ordS6A_Law947 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 947. -/
theorem noS6A_Law947 : ∀ v : Magma.tupS6A,
    ¬ @Equation947 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law947) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law947) (by native_decide) v.1 v.2
    ((@Law947.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 951 takes them (49 nodes). -/
def ordS6A_Law951 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 951. -/
theorem noS6A_Law951 : ∀ v : Magma.tupS6A,
    ¬ @Equation951 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law951) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law951) (by native_decide) v.1 v.2
    ((@Law951.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 955 takes them (49 nodes). -/
def ordS6A_Law955 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 955. -/
theorem noS6A_Law955 : ∀ v : Magma.tupS6A,
    ¬ @Equation955 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law955) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law955) (by native_decide) v.1 v.2
    ((@Law955.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 960 takes them (189 nodes). -/
def ordS6A_Law960 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 960. -/
theorem noS6A_Law960 : ∀ v : Magma.tupS6A,
    ¬ @Equation960 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law960) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law960) (by native_decide) v.1 v.2
    ((@Law960.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 968 takes them (92 nodes). -/
def ordS6A_Law968 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 968. -/
theorem noS6A_Law968 : ∀ v : Magma.tupS6A,
    ¬ @Equation968 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law968) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law968) (by native_decide) v.1 v.2
    ((@Law968.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 972 takes them (68 nodes). -/
def ordS6A_Law972 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 972. -/
theorem noS6A_Law972 : ∀ v : Magma.tupS6A,
    ¬ @Equation972 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law972) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law972) (by native_decide) v.1 v.2
    ((@Law972.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 977 takes them (323 nodes). -/
def ordS6A_Law977 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 977. -/
theorem noS6A_Law977 : ∀ v : Magma.tupS6A,
    ¬ @Equation977 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law977) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law977) (by native_decide) v.1 v.2
    ((@Law977.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 985 takes them (117 nodes). -/
def ordS6A_Law985 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 985. -/
theorem noS6A_Law985 : ∀ v : Magma.tupS6A,
    ¬ @Equation985 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law985) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law985) (by native_decide) v.1 v.2
    ((@Law985.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 989 takes them (108 nodes). -/
def ordS6A_Law989 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 989. -/
theorem noS6A_Law989 : ∀ v : Magma.tupS6A,
    ¬ @Equation989 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law989) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law989) (by native_decide) v.1 v.2
    ((@Law989.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 994 takes them (115 nodes). -/
def ordS6A_Law994 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 994. -/
theorem noS6A_Law994 : ∀ v : Magma.tupS6A,
    ¬ @Equation994 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law994) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law994) (by native_decide) v.1 v.2
    ((@Law994.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 999 takes them (37 nodes). -/
def ordS6A_Law999 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 999. -/
theorem noS6A_Law999 : ∀ v : Magma.tupS6A,
    ¬ @Equation999 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law999) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law999) (by native_decide) v.1 v.2
    ((@Law999.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1004 takes them (35 nodes). -/
def ordS6A_Law1004 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1004. -/
theorem noS6A_Law1004 : ∀ v : Magma.tupS6A,
    ¬ @Equation1004 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1004) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1004) (by native_decide) v.1 v.2
    ((@Law1004.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1009 takes them (66 nodes). -/
def ordS6A_Law1009 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1009. -/
theorem noS6A_Law1009 : ∀ v : Magma.tupS6A,
    ¬ @Equation1009 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1009) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1009) (by native_decide) v.1 v.2
    ((@Law1009.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1014 takes them (35 nodes). -/
def ordS6A_Law1014 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1014. -/
theorem noS6A_Law1014 : ∀ v : Magma.tupS6A,
    ¬ @Equation1014 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1014) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1014) (by native_decide) v.1 v.2
    ((@Law1014.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1040 takes them (53 nodes). -/
def ordS6A_Law1040 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1040. -/
theorem noS6A_Law1040 : ∀ v : Magma.tupS6A,
    ¬ @Equation1040 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1040) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1040) (by native_decide) v.1 v.2
    ((@Law1040.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1044 takes them (43 nodes). -/
def ordS6A_Law1044 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1044. -/
theorem noS6A_Law1044 : ∀ v : Magma.tupS6A,
    ¬ @Equation1044 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1044) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1044) (by native_decide) v.1 v.2
    ((@Law1044.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1047 takes them (57 nodes). -/
def ordS6A_Law1047 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1047. -/
theorem noS6A_Law1047 : ∀ v : Magma.tupS6A,
    ¬ @Equation1047 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1047) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1047) (by native_decide) v.1 v.2
    ((@Law1047.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1054 takes them (52 nodes). -/
def ordS6A_Law1054 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1054. -/
theorem noS6A_Law1054 : ∀ v : Magma.tupS6A,
    ¬ @Equation1054 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1054) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1054) (by native_decide) v.1 v.2
    ((@Law1054.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1057 takes them (104 nodes). -/
def ordS6A_Law1057 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1057. -/
theorem noS6A_Law1057 : ∀ v : Magma.tupS6A,
    ¬ @Equation1057 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1057) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1057) (by native_decide) v.1 v.2
    ((@Law1057.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1058 takes them (43 nodes). -/
def ordS6A_Law1058 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1058. -/
theorem noS6A_Law1058 : ∀ v : Magma.tupS6A,
    ¬ @Equation1058 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1058) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1058) (by native_decide) v.1 v.2
    ((@Law1058.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1062 takes them (49 nodes). -/
def ordS6A_Law1062 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1062. -/
theorem noS6A_Law1062 : ∀ v : Magma.tupS6A,
    ¬ @Equation1062 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1062) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1062) (by native_decide) v.1 v.2
    ((@Law1062.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1065 takes them (124 nodes). -/
def ordS6A_Law1065 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1065. -/
theorem noS6A_Law1065 : ∀ v : Magma.tupS6A,
    ¬ @Equation1065 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1065) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1065) (by native_decide) v.1 v.2
    ((@Law1065.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1066 takes them (68 nodes). -/
def ordS6A_Law1066 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1066. -/
theorem noS6A_Law1066 : ∀ v : Magma.tupS6A,
    ¬ @Equation1066 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1066) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1066) (by native_decide) v.1 v.2
    ((@Law1066.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1069 takes them (81 nodes). -/
def ordS6A_Law1069 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1069. -/
theorem noS6A_Law1069 : ∀ v : Magma.tupS6A,
    ¬ @Equation1069 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1069) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1069) (by native_decide) v.1 v.2
    ((@Law1069.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1070 takes them (79 nodes). -/
def ordS6A_Law1070 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1070. -/
theorem noS6A_Law1070 : ∀ v : Magma.tupS6A,
    ¬ @Equation1070 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1070) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1070) (by native_decide) v.1 v.2
    ((@Law1070.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1071 takes them (41 nodes). -/
def ordS6A_Law1071 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1071. -/
theorem noS6A_Law1071 : ∀ v : Magma.tupS6A,
    ¬ @Equation1071 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1071) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1071) (by native_decide) v.1 v.2
    ((@Law1071.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `31` equations. -/
theorem srch6A_refutes_8 :
    FamilyRefutes Magma.srch6A [
      926, 930, 934, 938, 943, 947, 951, 955, 960, 968, 972, 977, 985, 989, 994, 999, 1004, 1009,
      1014, 1040, 1044, 1047, 1054, 1057, 1058, 1062, 1065, 1066, 1069, 1070, 1071
    ] :=
  ⟨noS6A_Law926, noS6A_Law930, noS6A_Law934, noS6A_Law938, noS6A_Law943, noS6A_Law947, noS6A_Law951, noS6A_Law955, noS6A_Law960, noS6A_Law968, noS6A_Law972, noS6A_Law977, noS6A_Law985, noS6A_Law989, noS6A_Law994, noS6A_Law999, noS6A_Law1004, noS6A_Law1009, noS6A_Law1014, noS6A_Law1040, noS6A_Law1044, noS6A_Law1047, noS6A_Law1054, noS6A_Law1057, noS6A_Law1058, noS6A_Law1062, noS6A_Law1065, noS6A_Law1066, noS6A_Law1069, noS6A_Law1070, noS6A_Law1071⟩

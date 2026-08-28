import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 42 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `29`
equations here, 2,085 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 882 takes them (540 nodes). -/
def ordS8R9_Law882 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 882. -/
theorem noS8R9_Law882 : ∀ v : Magma.tup8R9,
    ¬ @Equation882 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law882) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law882) (by native_decide) v.1 v.2
    ((@Law882.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 885 takes them (47 nodes). -/
def ordS8R9_Law885 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 885. -/
theorem noS8R9_Law885 : ∀ v : Magma.tup8R9,
    ¬ @Equation885 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law885) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law885) (by native_decide) v.1 v.2
    ((@Law885.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 889 takes them (9 nodes). -/
def ordS8R9_Law889 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 889. -/
theorem noS8R9_Law889 : ∀ v : Magma.tup8R9,
    ¬ @Equation889 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law889) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law889) (by native_decide) v.1 v.2
    ((@Law889.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 893 takes them (57 nodes). -/
def ordS8R9_Law893 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 893. -/
theorem noS8R9_Law893 : ∀ v : Magma.tup8R9,
    ¬ @Equation893 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law893) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law893) (by native_decide) v.1 v.2
    ((@Law893.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 897 takes them (9 nodes). -/
def ordS8R9_Law897 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 897. -/
theorem noS8R9_Law897 : ∀ v : Magma.tup8R9,
    ¬ @Equation897 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law897) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law897) (by native_decide) v.1 v.2
    ((@Law897.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 901 takes them (9 nodes). -/
def ordS8R9_Law901 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 901. -/
theorem noS8R9_Law901 : ∀ v : Magma.tup8R9,
    ¬ @Equation901 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law901) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law901) (by native_decide) v.1 v.2
    ((@Law901.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 912 takes them (184 nodes). -/
def ordS8R9_Law912 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 912. -/
theorem noS8R9_Law912 : ∀ v : Magma.tup8R9,
    ¬ @Equation912 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law912) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law912) (by native_decide) v.1 v.2
    ((@Law912.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 922 takes them (73 nodes). -/
def ordS8R9_Law922 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 922. -/
theorem noS8R9_Law922 : ∀ v : Magma.tup8R9,
    ¬ @Equation922 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law922) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law922) (by native_decide) v.1 v.2
    ((@Law922.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 926 takes them (31 nodes). -/
def ordS8R9_Law926 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 926. -/
theorem noS8R9_Law926 : ∀ v : Magma.tup8R9,
    ¬ @Equation926 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law926) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law926) (by native_decide) v.1 v.2
    ((@Law926.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 930 takes them (172 nodes). -/
def ordS8R9_Law930 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 930. -/
theorem noS8R9_Law930 : ∀ v : Magma.tup8R9,
    ¬ @Equation930 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law930) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law930) (by native_decide) v.1 v.2
    ((@Law930.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 934 takes them (81 nodes). -/
def ordS8R9_Law934 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 934. -/
theorem noS8R9_Law934 : ∀ v : Magma.tup8R9,
    ¬ @Equation934 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law934) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law934) (by native_decide) v.1 v.2
    ((@Law934.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 938 takes them (15 nodes). -/
def ordS8R9_Law938 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 938. -/
theorem noS8R9_Law938 : ∀ v : Magma.tup8R9,
    ¬ @Equation938 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law938) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law938) (by native_decide) v.1 v.2
    ((@Law938.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 943 takes them (9 nodes). -/
def ordS8R9_Law943 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 943. -/
theorem noS8R9_Law943 : ∀ v : Magma.tup8R9,
    ¬ @Equation943 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law943) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law943) (by native_decide) v.1 v.2
    ((@Law943.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 951 takes them (9 nodes). -/
def ordS8R9_Law951 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 951. -/
theorem noS8R9_Law951 : ∀ v : Magma.tup8R9,
    ¬ @Equation951 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law951) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law951) (by native_decide) v.1 v.2
    ((@Law951.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 955 takes them (9 nodes). -/
def ordS8R9_Law955 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 955. -/
theorem noS8R9_Law955 : ∀ v : Magma.tup8R9,
    ¬ @Equation955 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law955) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law955) (by native_decide) v.1 v.2
    ((@Law955.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 960 takes them (103 nodes). -/
def ordS8R9_Law960 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 960. -/
theorem noS8R9_Law960 : ∀ v : Magma.tup8R9,
    ¬ @Equation960 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law960) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law960) (by native_decide) v.1 v.2
    ((@Law960.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 964 takes them (70 nodes). -/
def ordS8R9_Law964 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 964. -/
theorem noS8R9_Law964 : ∀ v : Magma.tup8R9,
    ¬ @Equation964 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law964) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law964) (by native_decide) v.1 v.2
    ((@Law964.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 968 takes them (143 nodes). -/
def ordS8R9_Law968 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 968. -/
theorem noS8R9_Law968 : ∀ v : Magma.tup8R9,
    ¬ @Equation968 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law968) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law968) (by native_decide) v.1 v.2
    ((@Law968.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 972 takes them (13 nodes). -/
def ordS8R9_Law972 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 972. -/
theorem noS8R9_Law972 : ∀ v : Magma.tup8R9,
    ¬ @Equation972 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law972) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law972) (by native_decide) v.1 v.2
    ((@Law972.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 977 takes them (9 nodes). -/
def ordS8R9_Law977 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 977. -/
theorem noS8R9_Law977 : ∀ v : Magma.tup8R9,
    ¬ @Equation977 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law977) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law977) (by native_decide) v.1 v.2
    ((@Law977.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 981 takes them (19 nodes). -/
def ordS8R9_Law981 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 981. -/
theorem noS8R9_Law981 : ∀ v : Magma.tup8R9,
    ¬ @Equation981 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law981) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law981) (by native_decide) v.1 v.2
    ((@Law981.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 985 takes them (9 nodes). -/
def ordS8R9_Law985 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 985. -/
theorem noS8R9_Law985 : ∀ v : Magma.tup8R9,
    ¬ @Equation985 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law985) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law985) (by native_decide) v.1 v.2
    ((@Law985.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 989 takes them (9 nodes). -/
def ordS8R9_Law989 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 989. -/
theorem noS8R9_Law989 : ∀ v : Magma.tup8R9,
    ¬ @Equation989 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law989) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law989) (by native_decide) v.1 v.2
    ((@Law989.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 994 takes them (9 nodes). -/
def ordS8R9_Law994 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 994. -/
theorem noS8R9_Law994 : ∀ v : Magma.tup8R9,
    ¬ @Equation994 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law994) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law994) (by native_decide) v.1 v.2
    ((@Law994.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 999 takes them (19 nodes). -/
def ordS8R9_Law999 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 999. -/
theorem noS8R9_Law999 : ∀ v : Magma.tup8R9,
    ¬ @Equation999 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law999) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law999) (by native_decide) v.1 v.2
    ((@Law999.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1004 takes them (9 nodes). -/
def ordS8R9_Law1004 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1004. -/
theorem noS8R9_Law1004 : ∀ v : Magma.tup8R9,
    ¬ @Equation1004 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1004) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1004) (by native_decide) v.1 v.2
    ((@Law1004.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1009 takes them (9 nodes). -/
def ordS8R9_Law1009 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1009. -/
theorem noS8R9_Law1009 : ∀ v : Magma.tup8R9,
    ¬ @Equation1009 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1009) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1009) (by native_decide) v.1 v.2
    ((@Law1009.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1014 takes them (9 nodes). -/
def ordS8R9_Law1014 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1014. -/
theorem noS8R9_Law1014 : ∀ v : Magma.tup8R9,
    ¬ @Equation1014 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1014) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law1014) (by native_decide) v.1 v.2
    ((@Law1014.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1037 takes them (401 nodes). -/
def ordS8R9_Law1037 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1037. -/
theorem noS8R9_Law1037 : ∀ v : Magma.tup8R9,
    ¬ @Equation1037 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1037) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1037) (by native_decide) v.1 v.2
    ((@Law1037.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `29` equations. -/
theorem srch8R9_refutes_41 :
    FamilyRefutes Magma.srch8R9 [
      882, 885, 889, 893, 897, 901, 912, 922, 926, 930, 934, 938, 943, 951, 955, 960, 964, 968,
      972, 977, 981, 985, 989, 994, 999, 1004, 1009, 1014, 1037
    ] :=
  ⟨noS8R9_Law882, noS8R9_Law885, noS8R9_Law889, noS8R9_Law893, noS8R9_Law897, noS8R9_Law901, noS8R9_Law912, noS8R9_Law922, noS8R9_Law926, noS8R9_Law930, noS8R9_Law934, noS8R9_Law938, noS8R9_Law943, noS8R9_Law951, noS8R9_Law955, noS8R9_Law960, noS8R9_Law964, noS8R9_Law968, noS8R9_Law972, noS8R9_Law977, noS8R9_Law981, noS8R9_Law985, noS8R9_Law989, noS8R9_Law994, noS8R9_Law999, noS8R9_Law1004, noS8R9_Law1009, noS8R9_Law1014, noS8R9_Law1037⟩

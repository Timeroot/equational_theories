import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 20 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `16`
equations here, 3,271 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2041 takes them (312 nodes). -/
def ordS6A_Law2041 : List (Fin 11) := [0, 10, 4, 1, 2, 9, 5, 7, 3, 6, 8]

/-- No member of the class satisfies equation 2041. -/
theorem noS6A_Law2041 : ∀ v : Magma.tupS6A,
    ¬ @Equation2041 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2041) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2041) (by native_decide) v.1 v.2
    ((@Law2041.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2042 takes them (159 nodes). -/
def ordS6A_Law2042 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2042. -/
theorem noS6A_Law2042 : ∀ v : Magma.tupS6A,
    ¬ @Equation2042 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2042) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2042) (by native_decide) v.1 v.2
    ((@Law2042.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2045 takes them (169 nodes). -/
def ordS6A_Law2045 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2045. -/
theorem noS6A_Law2045 : ∀ v : Magma.tupS6A,
    ¬ @Equation2045 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2045) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2045) (by native_decide) v.1 v.2
    ((@Law2045.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2046 takes them (312 nodes). -/
def ordS6A_Law2046 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2046. -/
theorem noS6A_Law2046 : ∀ v : Magma.tupS6A,
    ¬ @Equation2046 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2046) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2046) (by native_decide) v.1 v.2
    ((@Law2046.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2047 takes them (233 nodes). -/
def ordS6A_Law2047 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2047. -/
theorem noS6A_Law2047 : ∀ v : Magma.tupS6A,
    ¬ @Equation2047 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2047) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2047) (by native_decide) v.1 v.2
    ((@Law2047.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2048 takes them (221 nodes). -/
def ordS6A_Law2048 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2048. -/
theorem noS6A_Law2048 : ∀ v : Magma.tupS6A,
    ¬ @Equation2048 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2048) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2048) (by native_decide) v.1 v.2
    ((@Law2048.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2049 takes them (132 nodes). -/
def ordS6A_Law2049 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2049. -/
theorem noS6A_Law2049 : ∀ v : Magma.tupS6A,
    ¬ @Equation2049 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2049) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2049) (by native_decide) v.1 v.2
    ((@Law2049.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2052 takes them (101 nodes). -/
def ordS6A_Law2052 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2052. -/
theorem noS6A_Law2052 : ∀ v : Magma.tupS6A,
    ¬ @Equation2052 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2052) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2052) (by native_decide) v.1 v.2
    ((@Law2052.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2054 takes them (424 nodes). -/
def ordS6A_Law2054 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2054. -/
theorem noS6A_Law2054 : ∀ v : Magma.tupS6A,
    ¬ @Equation2054 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2054) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2054) (by native_decide) v.1 v.2
    ((@Law2054.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2055 takes them (122 nodes). -/
def ordS6A_Law2055 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2055. -/
theorem noS6A_Law2055 : ∀ v : Magma.tupS6A,
    ¬ @Equation2055 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2055) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2055) (by native_decide) v.1 v.2
    ((@Law2055.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2056 takes them (284 nodes). -/
def ordS6A_Law2056 : List (Fin 11) := [0, 8, 10, 5, 6, 4, 7, 1, 3, 9, 2]

/-- No member of the class satisfies equation 2056. -/
theorem noS6A_Law2056 : ∀ v : Magma.tupS6A,
    ¬ @Equation2056 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2056) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2056) (by native_decide) v.1 v.2
    ((@Law2056.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2057 takes them (109 nodes). -/
def ordS6A_Law2057 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2057. -/
theorem noS6A_Law2057 : ∀ v : Magma.tupS6A,
    ¬ @Equation2057 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2057) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2057) (by native_decide) v.1 v.2
    ((@Law2057.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2058 takes them (154 nodes). -/
def ordS6A_Law2058 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2058. -/
theorem noS6A_Law2058 : ∀ v : Magma.tupS6A,
    ¬ @Equation2058 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2058) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2058) (by native_decide) v.1 v.2
    ((@Law2058.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2059 takes them (82 nodes). -/
def ordS6A_Law2059 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2059. -/
theorem noS6A_Law2059 : ∀ v : Magma.tupS6A,
    ¬ @Equation2059 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2059) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2059) (by native_decide) v.1 v.2
    ((@Law2059.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2061 takes them (391 nodes). -/
def ordS6A_Law2061 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2061. -/
theorem noS6A_Law2061 : ∀ v : Magma.tupS6A,
    ¬ @Equation2061 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2061) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2061) (by native_decide) v.1 v.2
    ((@Law2061.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2062 takes them (66 nodes). -/
def ordS6A_Law2062 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2062. -/
theorem noS6A_Law2062 : ∀ v : Magma.tupS6A,
    ¬ @Equation2062 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2062) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2062) (by native_decide) v.1 v.2
    ((@Law2062.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch6A_refutes_19 :
    FamilyRefutes Magma.srch6A [
      2041, 2042, 2045, 2046, 2047, 2048, 2049, 2052, 2054, 2055, 2056, 2057, 2058, 2059, 2061,
      2062
    ] :=
  ⟨noS6A_Law2041, noS6A_Law2042, noS6A_Law2045, noS6A_Law2046, noS6A_Law2047, noS6A_Law2048, noS6A_Law2049, noS6A_Law2052, noS6A_Law2054, noS6A_Law2055, noS6A_Law2056, noS6A_Law2057, noS6A_Law2058, noS6A_Law2059, noS6A_Law2061, noS6A_Law2062⟩

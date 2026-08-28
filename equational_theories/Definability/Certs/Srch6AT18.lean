import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 19 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `24`
equations here, 2,975 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1908 takes them (132 nodes). -/
def ordS6A_Law1908 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1908. -/
theorem noS6A_Law1908 : ∀ v : Magma.tupS6A,
    ¬ @Equation1908 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1908) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1908) (by native_decide) v.1 v.2
    ((@Law1908.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1912 takes them (197 nodes). -/
def ordS6A_Law1912 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1912. -/
theorem noS6A_Law1912 : ∀ v : Magma.tupS6A,
    ¬ @Equation1912 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1912) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1912) (by native_decide) v.1 v.2
    ((@Law1912.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1916 takes them (98 nodes). -/
def ordS6A_Law1916 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1916. -/
theorem noS6A_Law1916 : ∀ v : Magma.tupS6A,
    ¬ @Equation1916 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1916) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1916) (by native_decide) v.1 v.2
    ((@Law1916.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1924 takes them (384 nodes). -/
def ordS6A_Law1924 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1924. -/
theorem noS6A_Law1924 : ∀ v : Magma.tupS6A,
    ¬ @Equation1924 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1924) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1924) (by native_decide) v.1 v.2
    ((@Law1924.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1927 takes them (71 nodes). -/
def ordS6A_Law1927 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1927. -/
theorem noS6A_Law1927 : ∀ v : Magma.tupS6A,
    ¬ @Equation1927 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1927) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1927) (by native_decide) v.1 v.2
    ((@Law1927.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1937 takes them (85 nodes). -/
def ordS6A_Law1937 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1937. -/
theorem noS6A_Law1937 : ∀ v : Magma.tupS6A,
    ¬ @Equation1937 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1937) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1937) (by native_decide) v.1 v.2
    ((@Law1937.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1941 takes them (218 nodes). -/
def ordS6A_Law1941 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1941. -/
theorem noS6A_Law1941 : ∀ v : Magma.tupS6A,
    ¬ @Equation1941 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1941) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1941) (by native_decide) v.1 v.2
    ((@Law1941.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1945 takes them (56 nodes). -/
def ordS6A_Law1945 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1945. -/
theorem noS6A_Law1945 : ∀ v : Magma.tupS6A,
    ¬ @Equation1945 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1945) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1945) (by native_decide) v.1 v.2
    ((@Law1945.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1953 takes them (51 nodes). -/
def ordS6A_Law1953 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1953. -/
theorem noS6A_Law1953 : ∀ v : Magma.tupS6A,
    ¬ @Equation1953 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1953) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1953) (by native_decide) v.1 v.2
    ((@Law1953.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1962 takes them (106 nodes). -/
def ordS6A_Law1962 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1962. -/
theorem noS6A_Law1962 : ∀ v : Magma.tupS6A,
    ¬ @Equation1962 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1962) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1962) (by native_decide) v.1 v.2
    ((@Law1962.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1966 takes them (105 nodes). -/
def ordS6A_Law1966 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1966. -/
theorem noS6A_Law1966 : ∀ v : Magma.tupS6A,
    ¬ @Equation1966 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1966) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1966) (by native_decide) v.1 v.2
    ((@Law1966.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1970 takes them (56 nodes). -/
def ordS6A_Law1970 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1970. -/
theorem noS6A_Law1970 : ∀ v : Magma.tupS6A,
    ¬ @Equation1970 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1970) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1970) (by native_decide) v.1 v.2
    ((@Law1970.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1979 takes them (120 nodes). -/
def ordS6A_Law1979 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1979. -/
theorem noS6A_Law1979 : ∀ v : Magma.tupS6A,
    ¬ @Equation1979 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1979) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1979) (by native_decide) v.1 v.2
    ((@Law1979.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1983 takes them (145 nodes). -/
def ordS6A_Law1983 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1983. -/
theorem noS6A_Law1983 : ∀ v : Magma.tupS6A,
    ¬ @Equation1983 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1983) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1983) (by native_decide) v.1 v.2
    ((@Law1983.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1987 takes them (65 nodes). -/
def ordS6A_Law1987 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1987. -/
theorem noS6A_Law1987 : ∀ v : Magma.tupS6A,
    ¬ @Equation1987 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1987) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1987) (by native_decide) v.1 v.2
    ((@Law1987.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1992 takes them (318 nodes). -/
def ordS6A_Law1992 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1992. -/
theorem noS6A_Law1992 : ∀ v : Magma.tupS6A,
    ¬ @Equation1992 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1992) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1992) (by native_decide) v.1 v.2
    ((@Law1992.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2000 takes them (135 nodes). -/
def ordS6A_Law2000 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2000. -/
theorem noS6A_Law2000 : ∀ v : Magma.tupS6A,
    ¬ @Equation2000 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2000) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2000) (by native_decide) v.1 v.2
    ((@Law2000.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2004 takes them (85 nodes). -/
def ordS6A_Law2004 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2004. -/
theorem noS6A_Law2004 : ∀ v : Magma.tupS6A,
    ¬ @Equation2004 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2004) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2004) (by native_decide) v.1 v.2
    ((@Law2004.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2009 takes them (147 nodes). -/
def ordS6A_Law2009 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2009. -/
theorem noS6A_Law2009 : ∀ v : Magma.tupS6A,
    ¬ @Equation2009 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2009) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2009) (by native_decide) v.1 v.2
    ((@Law2009.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2014 takes them (51 nodes). -/
def ordS6A_Law2014 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2014. -/
theorem noS6A_Law2014 : ∀ v : Magma.tupS6A,
    ¬ @Equation2014 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2014) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2014) (by native_decide) v.1 v.2
    ((@Law2014.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2019 takes them (48 nodes). -/
def ordS6A_Law2019 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2019. -/
theorem noS6A_Law2019 : ∀ v : Magma.tupS6A,
    ¬ @Equation2019 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2019) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2019) (by native_decide) v.1 v.2
    ((@Law2019.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2024 takes them (68 nodes). -/
def ordS6A_Law2024 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2024. -/
theorem noS6A_Law2024 : ∀ v : Magma.tupS6A,
    ¬ @Equation2024 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2024) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2024) (by native_decide) v.1 v.2
    ((@Law2024.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2029 takes them (46 nodes). -/
def ordS6A_Law2029 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2029. -/
theorem noS6A_Law2029 : ∀ v : Magma.tupS6A,
    ¬ @Equation2029 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2029) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2029) (by native_decide) v.1 v.2
    ((@Law2029.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2039 takes them (188 nodes). -/
def ordS6A_Law2039 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2039. -/
theorem noS6A_Law2039 : ∀ v : Magma.tupS6A,
    ¬ @Equation2039 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2039) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2039) (by native_decide) v.1 v.2
    ((@Law2039.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `24` equations. -/
theorem srch6A_refutes_18 :
    FamilyRefutes Magma.srch6A [
      1908, 1912, 1916, 1924, 1927, 1937, 1941, 1945, 1953, 1962, 1966, 1970, 1979, 1983, 1987,
      1992, 2000, 2004, 2009, 2014, 2019, 2024, 2029, 2039
    ] :=
  ⟨noS6A_Law1908, noS6A_Law1912, noS6A_Law1916, noS6A_Law1924, noS6A_Law1927, noS6A_Law1937, noS6A_Law1941, noS6A_Law1945, noS6A_Law1953, noS6A_Law1962, noS6A_Law1966, noS6A_Law1970, noS6A_Law1979, noS6A_Law1983, noS6A_Law1987, noS6A_Law1992, noS6A_Law2000, noS6A_Law2004, noS6A_Law2009, noS6A_Law2014, noS6A_Law2019, noS6A_Law2024, noS6A_Law2029, noS6A_Law2039⟩

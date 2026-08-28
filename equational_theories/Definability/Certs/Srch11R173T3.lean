import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 4 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 320 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1860 takes them (4 nodes). -/
def ordS11R173_Law1860 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1860. -/
theorem noS11R173_Law1860 : ∀ v : Magma.tup11R173,
    ¬ @Equation1860 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1860) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1860) (by native_decide) v.1 v.2
    ((@Law1860.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1867 takes them (4 nodes). -/
def ordS11R173_Law1867 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1867. -/
theorem noS11R173_Law1867 : ∀ v : Magma.tup11R173,
    ¬ @Equation1867 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1867) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1867) (by native_decide) v.1 v.2
    ((@Law1867.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1884 takes them (3 nodes). -/
def ordS11R173_Law1884 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1884. -/
theorem noS11R173_Law1884 : ∀ v : Magma.tup11R173,
    ¬ @Equation1884 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1884) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1884) (by native_decide) v.1 v.2
    ((@Law1884.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (3 nodes). -/
def ordS11R173_Law1894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1894. -/
theorem noS11R173_Law1894 : ∀ v : Magma.tup11R173,
    ¬ @Equation1894 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (3 nodes). -/
def ordS11R173_Law1897 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1897. -/
theorem noS11R173_Law1897 : ∀ v : Magma.tup11R173,
    ¬ @Equation1897 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1958 takes them (3 nodes). -/
def ordS11R173_Law1958 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1958. -/
theorem noS11R173_Law1958 : ∀ v : Magma.tup11R173,
    ¬ @Equation1958 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1958) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1958) (by native_decide) v.1 v.2
    ((@Law1958.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2036 takes them (3 nodes). -/
def ordS11R173_Law2036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2036. -/
theorem noS11R173_Law2036 : ∀ v : Magma.tup11R173,
    ¬ @Equation2036 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2036) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2036) (by native_decide) v.1 v.2
    ((@Law2036.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2037 takes them (4 nodes). -/
def ordS11R173_Law2037 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2037. -/
theorem noS11R173_Law2037 : ∀ v : Magma.tup11R173,
    ¬ @Equation2037 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2037) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2037) (by native_decide) v.1 v.2
    ((@Law2037.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2040 takes them (4 nodes). -/
def ordS11R173_Law2040 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2040. -/
theorem noS11R173_Law2040 : ∀ v : Magma.tup11R173,
    ¬ @Equation2040 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2040) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2040) (by native_decide) v.1 v.2
    ((@Law2040.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2043 takes them (4 nodes). -/
def ordS11R173_Law2043 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2043. -/
theorem noS11R173_Law2043 : ∀ v : Magma.tup11R173,
    ¬ @Equation2043 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2050 takes them (4 nodes). -/
def ordS11R173_Law2050 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2050. -/
theorem noS11R173_Law2050 : ∀ v : Magma.tup11R173,
    ¬ @Equation2050 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2050) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2050) (by native_decide) v.1 v.2
    ((@Law2050.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (3 nodes). -/
def ordS11R173_Law2051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2051. -/
theorem noS11R173_Law2051 : ∀ v : Magma.tup11R173,
    ¬ @Equation2051 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2054 takes them (3 nodes). -/
def ordS11R173_Law2054 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2054. -/
theorem noS11R173_Law2054 : ∀ v : Magma.tup11R173,
    ¬ @Equation2054 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2054) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2054) (by native_decide) v.1 v.2
    ((@Law2054.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2056 takes them (4 nodes). -/
def ordS11R173_Law2056 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2056. -/
theorem noS11R173_Law2056 : ∀ v : Magma.tup11R173,
    ¬ @Equation2056 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2056) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2056) (by native_decide) v.1 v.2
    ((@Law2056.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2061 takes them (3 nodes). -/
def ordS11R173_Law2061 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2061. -/
theorem noS11R173_Law2061 : ∀ v : Magma.tup11R173,
    ¬ @Equation2061 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2061) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2061) (by native_decide) v.1 v.2
    ((@Law2061.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (3 nodes). -/
def ordS11R173_Law2064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2064. -/
theorem noS11R173_Law2064 : ∀ v : Magma.tup11R173,
    ¬ @Equation2064 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2070 takes them (4 nodes). -/
def ordS11R173_Law2070 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2070. -/
theorem noS11R173_Law2070 : ∀ v : Magma.tup11R173,
    ¬ @Equation2070 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2070) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2070) (by native_decide) v.1 v.2
    ((@Law2070.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2087 takes them (3 nodes). -/
def ordS11R173_Law2087 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2087. -/
theorem noS11R173_Law2087 : ∀ v : Magma.tup11R173,
    ¬ @Equation2087 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2087) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2087) (by native_decide) v.1 v.2
    ((@Law2087.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (3 nodes). -/
def ordS11R173_Law2090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2090. -/
theorem noS11R173_Law2090 : ∀ v : Magma.tup11R173,
    ¬ @Equation2090 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2093 takes them (3 nodes). -/
def ordS11R173_Law2093 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2093. -/
theorem noS11R173_Law2093 : ∀ v : Magma.tup11R173,
    ¬ @Equation2093 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2093) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2093) (by native_decide) v.1 v.2
    ((@Law2093.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2100 takes them (3 nodes). -/
def ordS11R173_Law2100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2100. -/
theorem noS11R173_Law2100 : ∀ v : Magma.tup11R173,
    ¬ @Equation2100 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2100) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2100) (by native_decide) v.1 v.2
    ((@Law2100.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2124 takes them (3 nodes). -/
def ordS11R173_Law2124 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2124. -/
theorem noS11R173_Law2124 : ∀ v : Magma.tup11R173,
    ¬ @Equation2124 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2124) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2124) (by native_decide) v.1 v.2
    ((@Law2124.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2161 takes them (3 nodes). -/
def ordS11R173_Law2161 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2161. -/
theorem noS11R173_Law2161 : ∀ v : Magma.tup11R173,
    ¬ @Equation2161 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2161) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2161) (by native_decide) v.1 v.2
    ((@Law2161.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2240 takes them (4 nodes). -/
def ordS11R173_Law2240 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2240. -/
theorem noS11R173_Law2240 : ∀ v : Magma.tup11R173,
    ¬ @Equation2240 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2240) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2240) (by native_decide) v.1 v.2
    ((@Law2240.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2243 takes them (4 nodes). -/
def ordS11R173_Law2243 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2243. -/
theorem noS11R173_Law2243 : ∀ v : Magma.tup11R173,
    ¬ @Equation2243 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2243) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2243) (by native_decide) v.1 v.2
    ((@Law2243.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2246 takes them (4 nodes). -/
def ordS11R173_Law2246 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2246. -/
theorem noS11R173_Law2246 : ∀ v : Magma.tup11R173,
    ¬ @Equation2246 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2246) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2246) (by native_decide) v.1 v.2
    ((@Law2246.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2249 takes them (4 nodes). -/
def ordS11R173_Law2249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2249. -/
theorem noS11R173_Law2249 : ∀ v : Magma.tup11R173,
    ¬ @Equation2249 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2249) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2249) (by native_decide) v.1 v.2
    ((@Law2249.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2253 takes them (4 nodes). -/
def ordS11R173_Law2253 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2253. -/
theorem noS11R173_Law2253 : ∀ v : Magma.tup11R173,
    ¬ @Equation2253 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2253) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2253) (by native_decide) v.1 v.2
    ((@Law2253.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (3 nodes). -/
def ordS11R173_Law2254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2254. -/
theorem noS11R173_Law2254 : ∀ v : Magma.tup11R173,
    ¬ @Equation2254 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2256 takes them (4 nodes). -/
def ordS11R173_Law2256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2256. -/
theorem noS11R173_Law2256 : ∀ v : Magma.tup11R173,
    ¬ @Equation2256 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2256) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2256) (by native_decide) v.1 v.2
    ((@Law2256.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2259 takes them (4 nodes). -/
def ordS11R173_Law2259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2259. -/
theorem noS11R173_Law2259 : ∀ v : Magma.tup11R173,
    ¬ @Equation2259 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2259) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2259) (by native_decide) v.1 v.2
    ((@Law2259.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2266 takes them (4 nodes). -/
def ordS11R173_Law2266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2266. -/
theorem noS11R173_Law2266 : ∀ v : Magma.tup11R173,
    ¬ @Equation2266 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2266) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2266) (by native_decide) v.1 v.2
    ((@Law2266.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2269 takes them (4 nodes). -/
def ordS11R173_Law2269 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2269. -/
theorem noS11R173_Law2269 : ∀ v : Magma.tup11R173,
    ¬ @Equation2269 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2269) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2269) (by native_decide) v.1 v.2
    ((@Law2269.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2273 takes them (4 nodes). -/
def ordS11R173_Law2273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2273. -/
theorem noS11R173_Law2273 : ∀ v : Magma.tup11R173,
    ¬ @Equation2273 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2273) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2273) (by native_decide) v.1 v.2
    ((@Law2273.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2277 takes them (4 nodes). -/
def ordS11R173_Law2277 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2277. -/
theorem noS11R173_Law2277 : ∀ v : Magma.tup11R173,
    ¬ @Equation2277 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2277) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2277) (by native_decide) v.1 v.2
    ((@Law2277.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2281 takes them (4 nodes). -/
def ordS11R173_Law2281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2281. -/
theorem noS11R173_Law2281 : ∀ v : Magma.tup11R173,
    ¬ @Equation2281 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2281) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2281) (by native_decide) v.1 v.2
    ((@Law2281.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2285 takes them (4 nodes). -/
def ordS11R173_Law2285 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2285. -/
theorem noS11R173_Law2285 : ∀ v : Magma.tup11R173,
    ¬ @Equation2285 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2285) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2285) (by native_decide) v.1 v.2
    ((@Law2285.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2290 takes them (3 nodes). -/
def ordS11R173_Law2290 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2290. -/
theorem noS11R173_Law2290 : ∀ v : Magma.tup11R173,
    ¬ @Equation2290 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2290) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2290) (by native_decide) v.1 v.2
    ((@Law2290.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (3 nodes). -/
def ordS11R173_Law2300 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2300. -/
theorem noS11R173_Law2300 : ∀ v : Magma.tup11R173,
    ¬ @Equation2300 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (3 nodes). -/
def ordS11R173_Law2303 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2303. -/
theorem noS11R173_Law2303 : ∀ v : Magma.tup11R173,
    ¬ @Equation2303 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2306 takes them (3 nodes). -/
def ordS11R173_Law2306 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2306. -/
theorem noS11R173_Law2306 : ∀ v : Magma.tup11R173,
    ¬ @Equation2306 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2306) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2306) (by native_decide) v.1 v.2
    ((@Law2306.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2310 takes them (3 nodes). -/
def ordS11R173_Law2310 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2310. -/
theorem noS11R173_Law2310 : ∀ v : Magma.tup11R173,
    ¬ @Equation2310 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2310) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2310) (by native_decide) v.1 v.2
    ((@Law2310.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2314 takes them (3 nodes). -/
def ordS11R173_Law2314 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2314. -/
theorem noS11R173_Law2314 : ∀ v : Magma.tup11R173,
    ¬ @Equation2314 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2314) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2314) (by native_decide) v.1 v.2
    ((@Law2314.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2337 takes them (3 nodes). -/
def ordS11R173_Law2337 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2337. -/
theorem noS11R173_Law2337 : ∀ v : Magma.tup11R173,
    ¬ @Equation2337 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2337) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2337) (by native_decide) v.1 v.2
    ((@Law2337.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2347 takes them (3 nodes). -/
def ordS11R173_Law2347 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2347. -/
theorem noS11R173_Law2347 : ∀ v : Magma.tup11R173,
    ¬ @Equation2347 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2347) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2347) (by native_decide) v.1 v.2
    ((@Law2347.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2364 takes them (3 nodes). -/
def ordS11R173_Law2364 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2364. -/
theorem noS11R173_Law2364 : ∀ v : Magma.tup11R173,
    ¬ @Equation2364 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2364) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2364) (by native_decide) v.1 v.2
    ((@Law2364.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2381 takes them (3 nodes). -/
def ordS11R173_Law2381 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2381. -/
theorem noS11R173_Law2381 : ∀ v : Magma.tup11R173,
    ¬ @Equation2381 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2381) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2381) (by native_decide) v.1 v.2
    ((@Law2381.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2398 takes them (3 nodes). -/
def ordS11R173_Law2398 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2398. -/
theorem noS11R173_Law2398 : ∀ v : Magma.tup11R173,
    ¬ @Equation2398 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2398) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2398) (by native_decide) v.1 v.2
    ((@Law2398.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2415 takes them (3 nodes). -/
def ordS11R173_Law2415 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2415. -/
theorem noS11R173_Law2415 : ∀ v : Magma.tup11R173,
    ¬ @Equation2415 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2415) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2415) (by native_decide) v.1 v.2
    ((@Law2415.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2443 takes them (4 nodes). -/
def ordS11R173_Law2443 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2443. -/
theorem noS11R173_Law2443 : ∀ v : Magma.tup11R173,
    ¬ @Equation2443 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2443) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2443) (by native_decide) v.1 v.2
    ((@Law2443.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2446 takes them (4 nodes). -/
def ordS11R173_Law2446 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2446. -/
theorem noS11R173_Law2446 : ∀ v : Magma.tup11R173,
    ¬ @Equation2446 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2452 takes them (4 nodes). -/
def ordS11R173_Law2452 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2452. -/
theorem noS11R173_Law2452 : ∀ v : Magma.tup11R173,
    ¬ @Equation2452 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2452) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2452) (by native_decide) v.1 v.2
    ((@Law2452.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2456 takes them (4 nodes). -/
def ordS11R173_Law2456 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2456. -/
theorem noS11R173_Law2456 : ∀ v : Magma.tup11R173,
    ¬ @Equation2456 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2456) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2456) (by native_decide) v.1 v.2
    ((@Law2456.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2459 takes them (4 nodes). -/
def ordS11R173_Law2459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2459. -/
theorem noS11R173_Law2459 : ∀ v : Magma.tup11R173,
    ¬ @Equation2459 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2459) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2459) (by native_decide) v.1 v.2
    ((@Law2459.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2462 takes them (4 nodes). -/
def ordS11R173_Law2462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2462. -/
theorem noS11R173_Law2462 : ∀ v : Magma.tup11R173,
    ¬ @Equation2462 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2462) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2462) (by native_decide) v.1 v.2
    ((@Law2462.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2466 takes them (4 nodes). -/
def ordS11R173_Law2466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2466. -/
theorem noS11R173_Law2466 : ∀ v : Magma.tup11R173,
    ¬ @Equation2466 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2466) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2466) (by native_decide) v.1 v.2
    ((@Law2466.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2467 takes them (3 nodes). -/
def ordS11R173_Law2467 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2467. -/
theorem noS11R173_Law2467 : ∀ v : Magma.tup11R173,
    ¬ @Equation2467 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2467) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2467) (by native_decide) v.1 v.2
    ((@Law2467.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2469 takes them (4 nodes). -/
def ordS11R173_Law2469 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2469. -/
theorem noS11R173_Law2469 : ∀ v : Magma.tup11R173,
    ¬ @Equation2469 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2469) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2469) (by native_decide) v.1 v.2
    ((@Law2469.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2472 takes them (4 nodes). -/
def ordS11R173_Law2472 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2472. -/
theorem noS11R173_Law2472 : ∀ v : Magma.tup11R173,
    ¬ @Equation2472 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2472) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2472) (by native_decide) v.1 v.2
    ((@Law2472.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2476 takes them (4 nodes). -/
def ordS11R173_Law2476 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2476. -/
theorem noS11R173_Law2476 : ∀ v : Magma.tup11R173,
    ¬ @Equation2476 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2480 takes them (4 nodes). -/
def ordS11R173_Law2480 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2480. -/
theorem noS11R173_Law2480 : ∀ v : Magma.tup11R173,
    ¬ @Equation2480 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2480) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2480) (by native_decide) v.1 v.2
    ((@Law2480.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2484 takes them (4 nodes). -/
def ordS11R173_Law2484 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2484. -/
theorem noS11R173_Law2484 : ∀ v : Magma.tup11R173,
    ¬ @Equation2484 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2484) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2484) (by native_decide) v.1 v.2
    ((@Law2484.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2488 takes them (4 nodes). -/
def ordS11R173_Law2488 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2488. -/
theorem noS11R173_Law2488 : ∀ v : Magma.tup11R173,
    ¬ @Equation2488 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2488) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2488) (by native_decide) v.1 v.2
    ((@Law2488.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2493 takes them (3 nodes). -/
def ordS11R173_Law2493 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2493. -/
theorem noS11R173_Law2493 : ∀ v : Magma.tup11R173,
    ¬ @Equation2493 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2493) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2493) (by native_decide) v.1 v.2
    ((@Law2493.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (3 nodes). -/
def ordS11R173_Law2496 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2496. -/
theorem noS11R173_Law2496 : ∀ v : Magma.tup11R173,
    ¬ @Equation2496 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2503 takes them (3 nodes). -/
def ordS11R173_Law2503 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2503. -/
theorem noS11R173_Law2503 : ∀ v : Magma.tup11R173,
    ¬ @Equation2503 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2503) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2503) (by native_decide) v.1 v.2
    ((@Law2503.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2513 takes them (3 nodes). -/
def ordS11R173_Law2513 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2513. -/
theorem noS11R173_Law2513 : ∀ v : Magma.tup11R173,
    ¬ @Equation2513 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2513) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2513) (by native_decide) v.1 v.2
    ((@Law2513.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2550 takes them (3 nodes). -/
def ordS11R173_Law2550 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2550. -/
theorem noS11R173_Law2550 : ∀ v : Magma.tup11R173,
    ¬ @Equation2550 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2550) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2550) (by native_decide) v.1 v.2
    ((@Law2550.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2567 takes them (3 nodes). -/
def ordS11R173_Law2567 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2567. -/
theorem noS11R173_Law2567 : ∀ v : Magma.tup11R173,
    ¬ @Equation2567 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2567) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2567) (by native_decide) v.1 v.2
    ((@Law2567.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2584 takes them (3 nodes). -/
def ordS11R173_Law2584 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2584. -/
theorem noS11R173_Law2584 : ∀ v : Magma.tup11R173,
    ¬ @Equation2584 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2584) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2584) (by native_decide) v.1 v.2
    ((@Law2584.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2601 takes them (3 nodes). -/
def ordS11R173_Law2601 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2601. -/
theorem noS11R173_Law2601 : ∀ v : Magma.tup11R173,
    ¬ @Equation2601 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2601) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2601) (by native_decide) v.1 v.2
    ((@Law2601.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2618 takes them (3 nodes). -/
def ordS11R173_Law2618 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2618. -/
theorem noS11R173_Law2618 : ∀ v : Magma.tup11R173,
    ¬ @Equation2618 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2618) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2618) (by native_decide) v.1 v.2
    ((@Law2618.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2646 takes them (4 nodes). -/
def ordS11R173_Law2646 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2646. -/
theorem noS11R173_Law2646 : ∀ v : Magma.tup11R173,
    ¬ @Equation2646 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2646) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2646) (by native_decide) v.1 v.2
    ((@Law2646.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2649 takes them (4 nodes). -/
def ordS11R173_Law2649 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2649. -/
theorem noS11R173_Law2649 : ∀ v : Magma.tup11R173,
    ¬ @Equation2649 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2649) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2649) (by native_decide) v.1 v.2
    ((@Law2649.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2650 takes them (3 nodes). -/
def ordS11R173_Law2650 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2650. -/
theorem noS11R173_Law2650 : ∀ v : Magma.tup11R173,
    ¬ @Equation2650 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2650) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2650) (by native_decide) v.1 v.2
    ((@Law2650.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2652 takes them (4 nodes). -/
def ordS11R173_Law2652 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2652. -/
theorem noS11R173_Law2652 : ∀ v : Magma.tup11R173,
    ¬ @Equation2652 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2652) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2652) (by native_decide) v.1 v.2
    ((@Law2652.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2655 takes them (4 nodes). -/
def ordS11R173_Law2655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2655. -/
theorem noS11R173_Law2655 : ∀ v : Magma.tup11R173,
    ¬ @Equation2655 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2655) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2655) (by native_decide) v.1 v.2
    ((@Law2655.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2659 takes them (4 nodes). -/
def ordS11R173_Law2659 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2659. -/
theorem noS11R173_Law2659 : ∀ v : Magma.tup11R173,
    ¬ @Equation2659 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2659) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2659) (by native_decide) v.1 v.2
    ((@Law2659.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (3 nodes). -/
def ordS11R173_Law2660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2660. -/
theorem noS11R173_Law2660 : ∀ v : Magma.tup11R173,
    ¬ @Equation2660 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2662 takes them (4 nodes). -/
def ordS11R173_Law2662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2662. -/
theorem noS11R173_Law2662 : ∀ v : Magma.tup11R173,
    ¬ @Equation2662 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2662) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2662) (by native_decide) v.1 v.2
    ((@Law2662.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (4 nodes). -/
def ordS11R173_Law2665 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2665. -/
theorem noS11R173_Law2665 : ∀ v : Magma.tup11R173,
    ¬ @Equation2665 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2669 takes them (4 nodes). -/
def ordS11R173_Law2669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2669. -/
theorem noS11R173_Law2669 : ∀ v : Magma.tup11R173,
    ¬ @Equation2669 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2669) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2669) (by native_decide) v.1 v.2
    ((@Law2669.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (3 nodes). -/
def ordS11R173_Law2673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2673. -/
theorem noS11R173_Law2673 : ∀ v : Magma.tup11R173,
    ¬ @Equation2673 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2675 takes them (4 nodes). -/
def ordS11R173_Law2675 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2675. -/
theorem noS11R173_Law2675 : ∀ v : Magma.tup11R173,
    ¬ @Equation2675 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2675) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2675) (by native_decide) v.1 v.2
    ((@Law2675.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (4 nodes). -/
def ordS11R173_Law2679 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2679. -/
theorem noS11R173_Law2679 : ∀ v : Magma.tup11R173,
    ¬ @Equation2679 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2683 takes them (4 nodes). -/
def ordS11R173_Law2683 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2683. -/
theorem noS11R173_Law2683 : ∀ v : Magma.tup11R173,
    ¬ @Equation2683 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2683) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2683) (by native_decide) v.1 v.2
    ((@Law2683.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2687 takes them (4 nodes). -/
def ordS11R173_Law2687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2687. -/
theorem noS11R173_Law2687 : ∀ v : Magma.tup11R173,
    ¬ @Equation2687 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2687) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2687) (by native_decide) v.1 v.2
    ((@Law2687.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2691 takes them (4 nodes). -/
def ordS11R173_Law2691 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2691. -/
theorem noS11R173_Law2691 : ∀ v : Magma.tup11R173,
    ¬ @Equation2691 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2691) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2691) (by native_decide) v.1 v.2
    ((@Law2691.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2696 takes them (3 nodes). -/
def ordS11R173_Law2696 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2696. -/
theorem noS11R173_Law2696 : ∀ v : Magma.tup11R173,
    ¬ @Equation2696 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2696) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2696) (by native_decide) v.1 v.2
    ((@Law2696.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (3 nodes). -/
def ordS11R173_Law2699 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2699. -/
theorem noS11R173_Law2699 : ∀ v : Magma.tup11R173,
    ¬ @Equation2699 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (3 nodes). -/
def ordS11R173_Law2702 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2702. -/
theorem noS11R173_Law2702 : ∀ v : Magma.tup11R173,
    ¬ @Equation2702 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch11R173_refutes_3 :
    FamilyRefutes Magma.srch11R173 [
      1860, 1867, 1884, 1894, 1897, 1958, 2036, 2037, 2040, 2043, 2050, 2051, 2054, 2056, 2061,
      2064, 2070, 2087, 2090, 2093, 2100, 2124, 2161, 2240, 2243, 2246, 2249, 2253, 2254, 2256,
      2259, 2266, 2269, 2273, 2277, 2281, 2285, 2290, 2300, 2303, 2306, 2310, 2314, 2337, 2347,
      2364, 2381, 2398, 2415, 2443, 2446, 2452, 2456, 2459, 2462, 2466, 2467, 2469, 2472, 2476,
      2480, 2484, 2488, 2493, 2496, 2503, 2513, 2550, 2567, 2584, 2601, 2618, 2646, 2649, 2650,
      2652, 2655, 2659, 2660, 2662, 2665, 2669, 2673, 2675, 2679, 2683, 2687, 2691, 2696, 2699,
      2702
    ] :=
  ⟨noS11R173_Law1860, noS11R173_Law1867, noS11R173_Law1884, noS11R173_Law1894, noS11R173_Law1897, noS11R173_Law1958, noS11R173_Law2036, noS11R173_Law2037, noS11R173_Law2040, noS11R173_Law2043, noS11R173_Law2050, noS11R173_Law2051, noS11R173_Law2054, noS11R173_Law2056, noS11R173_Law2061, noS11R173_Law2064, noS11R173_Law2070, noS11R173_Law2087, noS11R173_Law2090, noS11R173_Law2093, noS11R173_Law2100, noS11R173_Law2124, noS11R173_Law2161, noS11R173_Law2240, noS11R173_Law2243, noS11R173_Law2246, noS11R173_Law2249, noS11R173_Law2253, noS11R173_Law2254, noS11R173_Law2256, noS11R173_Law2259, noS11R173_Law2266, noS11R173_Law2269, noS11R173_Law2273, noS11R173_Law2277, noS11R173_Law2281, noS11R173_Law2285, noS11R173_Law2290, noS11R173_Law2300, noS11R173_Law2303, noS11R173_Law2306, noS11R173_Law2310, noS11R173_Law2314, noS11R173_Law2337, noS11R173_Law2347, noS11R173_Law2364, noS11R173_Law2381, noS11R173_Law2398, noS11R173_Law2415, noS11R173_Law2443, noS11R173_Law2446, noS11R173_Law2452, noS11R173_Law2456, noS11R173_Law2459, noS11R173_Law2462, noS11R173_Law2466, noS11R173_Law2467, noS11R173_Law2469, noS11R173_Law2472, noS11R173_Law2476, noS11R173_Law2480, noS11R173_Law2484, noS11R173_Law2488, noS11R173_Law2493, noS11R173_Law2496, noS11R173_Law2503, noS11R173_Law2513, noS11R173_Law2550, noS11R173_Law2567, noS11R173_Law2584, noS11R173_Law2601, noS11R173_Law2618, noS11R173_Law2646, noS11R173_Law2649, noS11R173_Law2650, noS11R173_Law2652, noS11R173_Law2655, noS11R173_Law2659, noS11R173_Law2660, noS11R173_Law2662, noS11R173_Law2665, noS11R173_Law2669, noS11R173_Law2673, noS11R173_Law2675, noS11R173_Law2679, noS11R173_Law2683, noS11R173_Law2687, noS11R173_Law2691, noS11R173_Law2696, noS11R173_Law2699, noS11R173_Law2702⟩

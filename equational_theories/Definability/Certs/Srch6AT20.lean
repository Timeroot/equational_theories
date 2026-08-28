import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 21 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `23`
equations here, 3,000 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2066 takes them (191 nodes). -/
def ordS6A_Law2066 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2066. -/
theorem noS6A_Law2066 : ∀ v : Magma.tupS6A,
    ¬ @Equation2066 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2066) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2066) (by native_decide) v.1 v.2
    ((@Law2066.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2067 takes them (66 nodes). -/
def ordS6A_Law2067 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2067. -/
theorem noS6A_Law2067 : ∀ v : Magma.tupS6A,
    ¬ @Equation2067 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2067) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2067) (by native_decide) v.1 v.2
    ((@Law2067.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2069 takes them (42 nodes). -/
def ordS6A_Law2069 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2069. -/
theorem noS6A_Law2069 : ∀ v : Magma.tupS6A,
    ¬ @Equation2069 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2069) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2069) (by native_decide) v.1 v.2
    ((@Law2069.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2071 takes them (125 nodes). -/
def ordS6A_Law2071 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2071. -/
theorem noS6A_Law2071 : ∀ v : Magma.tupS6A,
    ¬ @Equation2071 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2071) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2071) (by native_decide) v.1 v.2
    ((@Law2071.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2072 takes them (125 nodes). -/
def ordS6A_Law2072 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2072. -/
theorem noS6A_Law2072 : ∀ v : Magma.tupS6A,
    ¬ @Equation2072 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2072) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2072) (by native_decide) v.1 v.2
    ((@Law2072.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2073 takes them (54 nodes). -/
def ordS6A_Law2073 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2073. -/
theorem noS6A_Law2073 : ∀ v : Magma.tupS6A,
    ¬ @Equation2073 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2073) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2073) (by native_decide) v.1 v.2
    ((@Law2073.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2074 takes them (230 nodes). -/
def ordS6A_Law2074 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2074. -/
theorem noS6A_Law2074 : ∀ v : Magma.tupS6A,
    ¬ @Equation2074 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2074) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2074) (by native_decide) v.1 v.2
    ((@Law2074.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2075 takes them (183 nodes). -/
def ordS6A_Law2075 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2075. -/
theorem noS6A_Law2075 : ∀ v : Magma.tupS6A,
    ¬ @Equation2075 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2075) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2075) (by native_decide) v.1 v.2
    ((@Law2075.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2076 takes them (225 nodes). -/
def ordS6A_Law2076 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2076. -/
theorem noS6A_Law2076 : ∀ v : Magma.tupS6A,
    ¬ @Equation2076 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2076) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2076) (by native_decide) v.1 v.2
    ((@Law2076.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2077 takes them (83 nodes). -/
def ordS6A_Law2077 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2077. -/
theorem noS6A_Law2077 : ∀ v : Magma.tupS6A,
    ¬ @Equation2077 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2077) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2077) (by native_decide) v.1 v.2
    ((@Law2077.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2079 takes them (191 nodes). -/
def ordS6A_Law2079 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2079. -/
theorem noS6A_Law2079 : ∀ v : Magma.tupS6A,
    ¬ @Equation2079 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2079) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2079) (by native_decide) v.1 v.2
    ((@Law2079.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2080 takes them (183 nodes). -/
def ordS6A_Law2080 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2080. -/
theorem noS6A_Law2080 : ∀ v : Magma.tupS6A,
    ¬ @Equation2080 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2080) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2080) (by native_decide) v.1 v.2
    ((@Law2080.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2081 takes them (83 nodes). -/
def ordS6A_Law2081 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2081. -/
theorem noS6A_Law2081 : ∀ v : Magma.tupS6A,
    ¬ @Equation2081 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2081) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2081) (by native_decide) v.1 v.2
    ((@Law2081.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2082 takes them (152 nodes). -/
def ordS6A_Law2082 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2082. -/
theorem noS6A_Law2082 : ∀ v : Magma.tupS6A,
    ¬ @Equation2082 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2082) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2082) (by native_decide) v.1 v.2
    ((@Law2082.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2083 takes them (58 nodes). -/
def ordS6A_Law2083 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2083. -/
theorem noS6A_Law2083 : ∀ v : Magma.tupS6A,
    ¬ @Equation2083 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2083) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2083) (by native_decide) v.1 v.2
    ((@Law2083.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2084 takes them (58 nodes). -/
def ordS6A_Law2084 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2084. -/
theorem noS6A_Law2084 : ∀ v : Magma.tupS6A,
    ¬ @Equation2084 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2084) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2084) (by native_decide) v.1 v.2
    ((@Law2084.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2085 takes them (93 nodes). -/
def ordS6A_Law2085 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2085. -/
theorem noS6A_Law2085 : ∀ v : Magma.tupS6A,
    ¬ @Equation2085 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2085) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2085) (by native_decide) v.1 v.2
    ((@Law2085.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2086 takes them (36 nodes). -/
def ordS6A_Law2086 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2086. -/
theorem noS6A_Law2086 : ∀ v : Magma.tupS6A,
    ¬ @Equation2086 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2086) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2086) (by native_decide) v.1 v.2
    ((@Law2086.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2088 takes them (231 nodes). -/
def ordS6A_Law2088 : List (Fin 11) := [8, 6, 5, 1, 0, 4, 10, 7, 2, 9, 3]

/-- No member of the class satisfies equation 2088. -/
theorem noS6A_Law2088 : ∀ v : Magma.tupS6A,
    ¬ @Equation2088 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2088) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2088) (by native_decide) v.1 v.2
    ((@Law2088.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2093 takes them (76 nodes). -/
def ordS6A_Law2093 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2093. -/
theorem noS6A_Law2093 : ∀ v : Magma.tupS6A,
    ¬ @Equation2093 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2093) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2093) (by native_decide) v.1 v.2
    ((@Law2093.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2103 takes them (106 nodes). -/
def ordS6A_Law2103 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2103. -/
theorem noS6A_Law2103 : ∀ v : Magma.tupS6A,
    ¬ @Equation2103 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2103) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2103) (by native_decide) v.1 v.2
    ((@Law2103.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2107 takes them (309 nodes). -/
def ordS6A_Law2107 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2107. -/
theorem noS6A_Law2107 : ∀ v : Magma.tupS6A,
    ¬ @Equation2107 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2107) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2107) (by native_decide) v.1 v.2
    ((@Law2107.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2111 takes them (100 nodes). -/
def ordS6A_Law2111 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2111. -/
theorem noS6A_Law2111 : ∀ v : Magma.tupS6A,
    ¬ @Equation2111 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2111) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2111) (by native_decide) v.1 v.2
    ((@Law2111.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `23` equations. -/
theorem srch6A_refutes_20 :
    FamilyRefutes Magma.srch6A [
      2066, 2067, 2069, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2079, 2080, 2081, 2082, 2083,
      2084, 2085, 2086, 2088, 2093, 2103, 2107, 2111
    ] :=
  ⟨noS6A_Law2066, noS6A_Law2067, noS6A_Law2069, noS6A_Law2071, noS6A_Law2072, noS6A_Law2073, noS6A_Law2074, noS6A_Law2075, noS6A_Law2076, noS6A_Law2077, noS6A_Law2079, noS6A_Law2080, noS6A_Law2081, noS6A_Law2082, noS6A_Law2083, noS6A_Law2084, noS6A_Law2085, noS6A_Law2086, noS6A_Law2088, noS6A_Law2093, noS6A_Law2103, noS6A_Law2107, noS6A_Law2111⟩

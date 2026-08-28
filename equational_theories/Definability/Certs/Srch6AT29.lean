import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 30 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `27`
equations here, 2,865 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3063 takes them (217 nodes). -/
def ordS6A_Law3063 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3063. -/
theorem noS6A_Law3063 : ∀ v : Magma.tupS6A,
    ¬ @Equation3063 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3063) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3063) (by native_decide) v.1 v.2
    ((@Law3063.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3064 takes them (124 nodes). -/
def ordS6A_Law3064 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3064. -/
theorem noS6A_Law3064 : ∀ v : Magma.tupS6A,
    ¬ @Equation3064 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3064) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3064) (by native_decide) v.1 v.2
    ((@Law3064.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3067 takes them (90 nodes). -/
def ordS6A_Law3067 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3067. -/
theorem noS6A_Law3067 : ∀ v : Magma.tupS6A,
    ¬ @Equation3067 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3067) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3067) (by native_decide) v.1 v.2
    ((@Law3067.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3070 takes them (83 nodes). -/
def ordS6A_Law3070 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3070. -/
theorem noS6A_Law3070 : ∀ v : Magma.tupS6A,
    ¬ @Equation3070 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3070) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3070) (by native_decide) v.1 v.2
    ((@Law3070.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3072 takes them (155 nodes). -/
def ordS6A_Law3072 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3072. -/
theorem noS6A_Law3072 : ∀ v : Magma.tupS6A,
    ¬ @Equation3072 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3072) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3072) (by native_decide) v.1 v.2
    ((@Law3072.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3073 takes them (167 nodes). -/
def ordS6A_Law3073 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3073. -/
theorem noS6A_Law3073 : ∀ v : Magma.tupS6A,
    ¬ @Equation3073 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3073) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3073) (by native_decide) v.1 v.2
    ((@Law3073.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3074 takes them (73 nodes). -/
def ordS6A_Law3074 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3074. -/
theorem noS6A_Law3074 : ∀ v : Magma.tupS6A,
    ¬ @Equation3074 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3074) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3074) (by native_decide) v.1 v.2
    ((@Law3074.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3077 takes them (93 nodes). -/
def ordS6A_Law3077 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3077. -/
theorem noS6A_Law3077 : ∀ v : Magma.tupS6A,
    ¬ @Equation3077 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3077) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3077) (by native_decide) v.1 v.2
    ((@Law3077.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3080 takes them (34 nodes). -/
def ordS6A_Law3080 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3080. -/
theorem noS6A_Law3080 : ∀ v : Magma.tupS6A,
    ¬ @Equation3080 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3080) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3080) (by native_decide) v.1 v.2
    ((@Law3080.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3082 takes them (144 nodes). -/
def ordS6A_Law3082 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3082. -/
theorem noS6A_Law3082 : ∀ v : Magma.tupS6A,
    ¬ @Equation3082 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3082) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3082) (by native_decide) v.1 v.2
    ((@Law3082.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3084 takes them (34 nodes). -/
def ordS6A_Law3084 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3084. -/
theorem noS6A_Law3084 : ∀ v : Magma.tupS6A,
    ¬ @Equation3084 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3084) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3084) (by native_decide) v.1 v.2
    ((@Law3084.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3086 takes them (176 nodes). -/
def ordS6A_Law3086 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3086. -/
theorem noS6A_Law3086 : ∀ v : Magma.tupS6A,
    ¬ @Equation3086 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3086) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3086) (by native_decide) v.1 v.2
    ((@Law3086.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3087 takes them (164 nodes). -/
def ordS6A_Law3087 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3087. -/
theorem noS6A_Law3087 : ∀ v : Magma.tupS6A,
    ¬ @Equation3087 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3087) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3087) (by native_decide) v.1 v.2
    ((@Law3087.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3088 takes them (73 nodes). -/
def ordS6A_Law3088 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3088. -/
theorem noS6A_Law3088 : ∀ v : Magma.tupS6A,
    ¬ @Equation3088 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3088) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3088) (by native_decide) v.1 v.2
    ((@Law3088.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3090 takes them (150 nodes). -/
def ordS6A_Law3090 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3090. -/
theorem noS6A_Law3090 : ∀ v : Magma.tupS6A,
    ¬ @Equation3090 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3090) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3090) (by native_decide) v.1 v.2
    ((@Law3090.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3092 takes them (30 nodes). -/
def ordS6A_Law3092 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3092. -/
theorem noS6A_Law3092 : ∀ v : Magma.tupS6A,
    ¬ @Equation3092 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3092) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3092) (by native_decide) v.1 v.2
    ((@Law3092.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3095 takes them (144 nodes). -/
def ordS6A_Law3095 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3095. -/
theorem noS6A_Law3095 : ∀ v : Magma.tupS6A,
    ¬ @Equation3095 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3095) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3095) (by native_decide) v.1 v.2
    ((@Law3095.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3096 takes them (34 nodes). -/
def ordS6A_Law3096 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3096. -/
theorem noS6A_Law3096 : ∀ v : Magma.tupS6A,
    ¬ @Equation3096 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3096) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3096) (by native_decide) v.1 v.2
    ((@Law3096.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3098 takes them (140 nodes). -/
def ordS6A_Law3098 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3098. -/
theorem noS6A_Law3098 : ∀ v : Magma.tupS6A,
    ¬ @Equation3098 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3098) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3098) (by native_decide) v.1 v.2
    ((@Law3098.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3099 takes them (140 nodes). -/
def ordS6A_Law3099 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3099. -/
theorem noS6A_Law3099 : ∀ v : Magma.tupS6A,
    ¬ @Equation3099 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3099) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3099) (by native_decide) v.1 v.2
    ((@Law3099.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3100 takes them (140 nodes). -/
def ordS6A_Law3100 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3100. -/
theorem noS6A_Law3100 : ∀ v : Magma.tupS6A,
    ¬ @Equation3100 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3100) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3100) (by native_decide) v.1 v.2
    ((@Law3100.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3101 takes them (30 nodes). -/
def ordS6A_Law3101 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3101. -/
theorem noS6A_Law3101 : ∀ v : Magma.tupS6A,
    ¬ @Equation3101 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3101) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3101) (by native_decide) v.1 v.2
    ((@Law3101.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3118 takes them (86 nodes). -/
def ordS6A_Law3118 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3118. -/
theorem noS6A_Law3118 : ∀ v : Magma.tupS6A,
    ¬ @Equation3118 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3118) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3118) (by native_decide) v.1 v.2
    ((@Law3118.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3126 takes them (115 nodes). -/
def ordS6A_Law3126 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3126. -/
theorem noS6A_Law3126 : ∀ v : Magma.tupS6A,
    ¬ @Equation3126 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3126) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3126) (by native_decide) v.1 v.2
    ((@Law3126.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3130 takes them (76 nodes). -/
def ordS6A_Law3130 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3130. -/
theorem noS6A_Law3130 : ∀ v : Magma.tupS6A,
    ¬ @Equation3130 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3130) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3130) (by native_decide) v.1 v.2
    ((@Law3130.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3134 takes them (45 nodes). -/
def ordS6A_Law3134 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3134. -/
theorem noS6A_Law3134 : ∀ v : Magma.tupS6A,
    ¬ @Equation3134 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3134) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3134) (by native_decide) v.1 v.2
    ((@Law3134.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3155 takes them (108 nodes). -/
def ordS6A_Law3155 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3155. -/
theorem noS6A_Law3155 : ∀ v : Magma.tupS6A,
    ¬ @Equation3155 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3155) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3155) (by native_decide) v.1 v.2
    ((@Law3155.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `27` equations. -/
theorem srch6A_refutes_29 :
    FamilyRefutes Magma.srch6A [
      3063, 3064, 3067, 3070, 3072, 3073, 3074, 3077, 3080, 3082, 3084, 3086, 3087, 3088, 3090,
      3092, 3095, 3096, 3098, 3099, 3100, 3101, 3118, 3126, 3130, 3134, 3155
    ] :=
  ⟨noS6A_Law3063, noS6A_Law3064, noS6A_Law3067, noS6A_Law3070, noS6A_Law3072, noS6A_Law3073, noS6A_Law3074, noS6A_Law3077, noS6A_Law3080, noS6A_Law3082, noS6A_Law3084, noS6A_Law3086, noS6A_Law3087, noS6A_Law3088, noS6A_Law3090, noS6A_Law3092, noS6A_Law3095, noS6A_Law3096, noS6A_Law3098, noS6A_Law3099, noS6A_Law3100, noS6A_Law3101, noS6A_Law3118, noS6A_Law3126, noS6A_Law3130, noS6A_Law3134, noS6A_Law3155⟩

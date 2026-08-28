import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 29 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `26`
equations here, 2,841 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2912 takes them (345 nodes). -/
def ordS6A_Law2912 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2912. -/
theorem noS6A_Law2912 : ∀ v : Magma.tupS6A,
    ¬ @Equation2912 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2912) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2912) (by native_decide) v.1 v.2
    ((@Law2912.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2915 takes them (101 nodes). -/
def ordS6A_Law2915 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2915. -/
theorem noS6A_Law2915 : ∀ v : Magma.tupS6A,
    ¬ @Equation2915 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2915) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2915) (by native_decide) v.1 v.2
    ((@Law2915.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2923 takes them (130 nodes). -/
def ordS6A_Law2923 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2923. -/
theorem noS6A_Law2923 : ∀ v : Magma.tupS6A,
    ¬ @Equation2923 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2923) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2923) (by native_decide) v.1 v.2
    ((@Law2923.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2927 takes them (161 nodes). -/
def ordS6A_Law2927 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2927. -/
theorem noS6A_Law2927 : ∀ v : Magma.tupS6A,
    ¬ @Equation2927 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2927) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2927) (by native_decide) v.1 v.2
    ((@Law2927.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2931 takes them (88 nodes). -/
def ordS6A_Law2931 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2931. -/
theorem noS6A_Law2931 : ∀ v : Magma.tupS6A,
    ¬ @Equation2931 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2931) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2931) (by native_decide) v.1 v.2
    ((@Law2931.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2939 takes them (241 nodes). -/
def ordS6A_Law2939 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2939. -/
theorem noS6A_Law2939 : ∀ v : Magma.tupS6A,
    ¬ @Equation2939 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2939) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2939) (by native_decide) v.1 v.2
    ((@Law2939.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2942 takes them (75 nodes). -/
def ordS6A_Law2942 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2942. -/
theorem noS6A_Law2942 : ∀ v : Magma.tupS6A,
    ¬ @Equation2942 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2942) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2942) (by native_decide) v.1 v.2
    ((@Law2942.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2952 takes them (56 nodes). -/
def ordS6A_Law2952 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2952. -/
theorem noS6A_Law2952 : ∀ v : Magma.tupS6A,
    ¬ @Equation2952 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2952) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2952) (by native_decide) v.1 v.2
    ((@Law2952.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2960 takes them (72 nodes). -/
def ordS6A_Law2960 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2960. -/
theorem noS6A_Law2960 : ∀ v : Magma.tupS6A,
    ¬ @Equation2960 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2960) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2960) (by native_decide) v.1 v.2
    ((@Law2960.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2968 takes them (34 nodes). -/
def ordS6A_Law2968 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2968. -/
theorem noS6A_Law2968 : ∀ v : Magma.tupS6A,
    ¬ @Equation2968 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2968) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2968) (by native_decide) v.1 v.2
    ((@Law2968.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2977 takes them (112 nodes). -/
def ordS6A_Law2977 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2977. -/
theorem noS6A_Law2977 : ∀ v : Magma.tupS6A,
    ¬ @Equation2977 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2977) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2977) (by native_decide) v.1 v.2
    ((@Law2977.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2981 takes them (101 nodes). -/
def ordS6A_Law2981 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2981. -/
theorem noS6A_Law2981 : ∀ v : Magma.tupS6A,
    ¬ @Equation2981 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2981) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2981) (by native_decide) v.1 v.2
    ((@Law2981.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2985 takes them (69 nodes). -/
def ordS6A_Law2985 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2985. -/
theorem noS6A_Law2985 : ∀ v : Magma.tupS6A,
    ¬ @Equation2985 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2985) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2985) (by native_decide) v.1 v.2
    ((@Law2985.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2994 takes them (95 nodes). -/
def ordS6A_Law2994 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2994. -/
theorem noS6A_Law2994 : ∀ v : Magma.tupS6A,
    ¬ @Equation2994 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2994) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2994) (by native_decide) v.1 v.2
    ((@Law2994.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3002 takes them (36 nodes). -/
def ordS6A_Law3002 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3002. -/
theorem noS6A_Law3002 : ∀ v : Magma.tupS6A,
    ¬ @Equation3002 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3002) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3002) (by native_decide) v.1 v.2
    ((@Law3002.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3015 takes them (102 nodes). -/
def ordS6A_Law3015 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3015. -/
theorem noS6A_Law3015 : ∀ v : Magma.tupS6A,
    ¬ @Equation3015 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3015) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3015) (by native_decide) v.1 v.2
    ((@Law3015.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3019 takes them (56 nodes). -/
def ordS6A_Law3019 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3019. -/
theorem noS6A_Law3019 : ∀ v : Magma.tupS6A,
    ¬ @Equation3019 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3019) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3019) (by native_decide) v.1 v.2
    ((@Law3019.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3029 takes them (71 nodes). -/
def ordS6A_Law3029 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3029. -/
theorem noS6A_Law3029 : ∀ v : Magma.tupS6A,
    ¬ @Equation3029 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3029) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3029) (by native_decide) v.1 v.2
    ((@Law3029.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3034 takes them (57 nodes). -/
def ordS6A_Law3034 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3034. -/
theorem noS6A_Law3034 : ∀ v : Magma.tupS6A,
    ¬ @Equation3034 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3034) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3034) (by native_decide) v.1 v.2
    ((@Law3034.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3039 takes them (67 nodes). -/
def ordS6A_Law3039 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3039. -/
theorem noS6A_Law3039 : ∀ v : Magma.tupS6A,
    ¬ @Equation3039 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3039) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3039) (by native_decide) v.1 v.2
    ((@Law3039.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3044 takes them (29 nodes). -/
def ordS6A_Law3044 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3044. -/
theorem noS6A_Law3044 : ∀ v : Magma.tupS6A,
    ¬ @Equation3044 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3044) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3044) (by native_decide) v.1 v.2
    ((@Law3044.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3051 takes them (141 nodes). -/
def ordS6A_Law3051 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3051. -/
theorem noS6A_Law3051 : ∀ v : Magma.tupS6A,
    ¬ @Equation3051 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3051) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3051) (by native_decide) v.1 v.2
    ((@Law3051.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3054 takes them (141 nodes). -/
def ordS6A_Law3054 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3054. -/
theorem noS6A_Law3054 : ∀ v : Magma.tupS6A,
    ¬ @Equation3054 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3054) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3054) (by native_decide) v.1 v.2
    ((@Law3054.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3057 takes them (124 nodes). -/
def ordS6A_Law3057 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3057. -/
theorem noS6A_Law3057 : ∀ v : Magma.tupS6A,
    ¬ @Equation3057 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3057) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3057) (by native_decide) v.1 v.2
    ((@Law3057.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3060 takes them (124 nodes). -/
def ordS6A_Law3060 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3060. -/
theorem noS6A_Law3060 : ∀ v : Magma.tupS6A,
    ¬ @Equation3060 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3060) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3060) (by native_decide) v.1 v.2
    ((@Law3060.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3062 takes them (213 nodes). -/
def ordS6A_Law3062 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3062. -/
theorem noS6A_Law3062 : ∀ v : Magma.tupS6A,
    ¬ @Equation3062 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3062) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3062) (by native_decide) v.1 v.2
    ((@Law3062.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `26` equations. -/
theorem srch6A_refutes_28 :
    FamilyRefutes Magma.srch6A [
      2912, 2915, 2923, 2927, 2931, 2939, 2942, 2952, 2960, 2968, 2977, 2981, 2985, 2994, 3002,
      3015, 3019, 3029, 3034, 3039, 3044, 3051, 3054, 3057, 3060, 3062
    ] :=
  ⟨noS6A_Law2912, noS6A_Law2915, noS6A_Law2923, noS6A_Law2927, noS6A_Law2931, noS6A_Law2939, noS6A_Law2942, noS6A_Law2952, noS6A_Law2960, noS6A_Law2968, noS6A_Law2977, noS6A_Law2981, noS6A_Law2985, noS6A_Law2994, noS6A_Law3002, noS6A_Law3015, noS6A_Law3019, noS6A_Law3029, noS6A_Law3034, noS6A_Law3039, noS6A_Law3044, noS6A_Law3051, noS6A_Law3054, noS6A_Law3057, noS6A_Law3060, noS6A_Law3062⟩

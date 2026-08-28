import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 44 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `24`
equations here, 3,001 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3938 takes them (113 nodes). -/
def ordS6A_Law3938 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3938. -/
theorem noS6A_Law3938 : ∀ v : Magma.tupS6A,
    ¬ @Equation3938 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3938) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3938) (by native_decide) v.1 v.2
    ((@Law3938.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3940 takes them (170 nodes). -/
def ordS6A_Law3940 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3940. -/
theorem noS6A_Law3940 : ∀ v : Magma.tupS6A,
    ¬ @Equation3940 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3940) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3940) (by native_decide) v.1 v.2
    ((@Law3940.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3941 takes them (49 nodes). -/
def ordS6A_Law3941 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3941. -/
theorem noS6A_Law3941 : ∀ v : Magma.tupS6A,
    ¬ @Equation3941 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3941) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3941) (by native_decide) v.1 v.2
    ((@Law3941.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3942 takes them (104 nodes). -/
def ordS6A_Law3942 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3942. -/
theorem noS6A_Law3942 : ∀ v : Magma.tupS6A,
    ¬ @Equation3942 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3942) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3942) (by native_decide) v.1 v.2
    ((@Law3942.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3944 takes them (75 nodes). -/
def ordS6A_Law3944 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3944. -/
theorem noS6A_Law3944 : ∀ v : Magma.tupS6A,
    ¬ @Equation3944 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3944) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3944) (by native_decide) v.1 v.2
    ((@Law3944.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3945 takes them (75 nodes). -/
def ordS6A_Law3945 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3945. -/
theorem noS6A_Law3945 : ∀ v : Magma.tupS6A,
    ¬ @Equation3945 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3945) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3945) (by native_decide) v.1 v.2
    ((@Law3945.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3946 takes them (58 nodes). -/
def ordS6A_Law3946 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3946. -/
theorem noS6A_Law3946 : ∀ v : Magma.tupS6A,
    ¬ @Equation3946 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3946) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3946) (by native_decide) v.1 v.2
    ((@Law3946.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3948 takes them (45 nodes). -/
def ordS6A_Law3948 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3948. -/
theorem noS6A_Law3948 : ∀ v : Magma.tupS6A,
    ¬ @Equation3948 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3948) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3948) (by native_decide) v.1 v.2
    ((@Law3948.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3949 takes them (45 nodes). -/
def ordS6A_Law3949 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3949. -/
theorem noS6A_Law3949 : ∀ v : Magma.tupS6A,
    ¬ @Equation3949 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3949) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3949) (by native_decide) v.1 v.2
    ((@Law3949.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3950 takes them (45 nodes). -/
def ordS6A_Law3950 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3950. -/
theorem noS6A_Law3950 : ∀ v : Magma.tupS6A,
    ¬ @Equation3950 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3950) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3950) (by native_decide) v.1 v.2
    ((@Law3950.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3953 takes them (110 nodes). -/
def ordS6A_Law3953 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3953. -/
theorem noS6A_Law3953 : ∀ v : Magma.tupS6A,
    ¬ @Equation3953 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3953) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3953) (by native_decide) v.1 v.2
    ((@Law3953.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3956 takes them (74 nodes). -/
def ordS6A_Law3956 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3956. -/
theorem noS6A_Law3956 : ∀ v : Magma.tupS6A,
    ¬ @Equation3956 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3956) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3956) (by native_decide) v.1 v.2
    ((@Law3956.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3957 takes them (99 nodes). -/
def ordS6A_Law3957 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3957. -/
theorem noS6A_Law3957 : ∀ v : Magma.tupS6A,
    ¬ @Equation3957 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3957) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3957) (by native_decide) v.1 v.2
    ((@Law3957.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3958 takes them (162 nodes). -/
def ordS6A_Law3958 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3958. -/
theorem noS6A_Law3958 : ∀ v : Magma.tupS6A,
    ¬ @Equation3958 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3958) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3958) (by native_decide) v.1 v.2
    ((@Law3958.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3959 takes them (128 nodes). -/
def ordS6A_Law3959 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3959. -/
theorem noS6A_Law3959 : ∀ v : Magma.tupS6A,
    ¬ @Equation3959 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3959) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3959) (by native_decide) v.1 v.2
    ((@Law3959.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3960 takes them (44 nodes). -/
def ordS6A_Law3960 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3960. -/
theorem noS6A_Law3960 : ∀ v : Magma.tupS6A,
    ¬ @Equation3960 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3960) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3960) (by native_decide) v.1 v.2
    ((@Law3960.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3961 takes them (818 nodes). -/
def ordS6A_Law3961 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3961. -/
theorem noS6A_Law3961 : ∀ v : Magma.tupS6A,
    ¬ @Equation3961 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3961) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3961) (by native_decide) v.1 v.2
    ((@Law3961.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3963 takes them (75 nodes). -/
def ordS6A_Law3963 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3963. -/
theorem noS6A_Law3963 : ∀ v : Magma.tupS6A,
    ¬ @Equation3963 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3963) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3963) (by native_decide) v.1 v.2
    ((@Law3963.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3965 takes them (260 nodes). -/
def ordS6A_Law3965 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3965. -/
theorem noS6A_Law3965 : ∀ v : Magma.tupS6A,
    ¬ @Equation3965 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3965) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3965) (by native_decide) v.1 v.2
    ((@Law3965.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3966 takes them (85 nodes). -/
def ordS6A_Law3966 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3966. -/
theorem noS6A_Law3966 : ∀ v : Magma.tupS6A,
    ¬ @Equation3966 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3966) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3966) (by native_decide) v.1 v.2
    ((@Law3966.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3967 takes them (87 nodes). -/
def ordS6A_Law3967 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3967. -/
theorem noS6A_Law3967 : ∀ v : Magma.tupS6A,
    ¬ @Equation3967 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3967) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3967) (by native_decide) v.1 v.2
    ((@Law3967.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3968 takes them (153 nodes). -/
def ordS6A_Law3968 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3968. -/
theorem noS6A_Law3968 : ∀ v : Magma.tupS6A,
    ¬ @Equation3968 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3968) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3968) (by native_decide) v.1 v.2
    ((@Law3968.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3969 takes them (75 nodes). -/
def ordS6A_Law3969 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3969. -/
theorem noS6A_Law3969 : ∀ v : Magma.tupS6A,
    ¬ @Equation3969 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3969) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3969) (by native_decide) v.1 v.2
    ((@Law3969.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3970 takes them (52 nodes). -/
def ordS6A_Law3970 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3970. -/
theorem noS6A_Law3970 : ∀ v : Magma.tupS6A,
    ¬ @Equation3970 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3970) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3970) (by native_decide) v.1 v.2
    ((@Law3970.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `24` equations. -/
theorem srch6A_refutes_43 :
    FamilyRefutes Magma.srch6A [
      3938, 3940, 3941, 3942, 3944, 3945, 3946, 3948, 3949, 3950, 3953, 3956, 3957, 3958, 3959,
      3960, 3961, 3963, 3965, 3966, 3967, 3968, 3969, 3970
    ] :=
  ⟨noS6A_Law3938, noS6A_Law3940, noS6A_Law3941, noS6A_Law3942, noS6A_Law3944, noS6A_Law3945, noS6A_Law3946, noS6A_Law3948, noS6A_Law3949, noS6A_Law3950, noS6A_Law3953, noS6A_Law3956, noS6A_Law3957, noS6A_Law3958, noS6A_Law3959, noS6A_Law3960, noS6A_Law3961, noS6A_Law3963, noS6A_Law3965, noS6A_Law3966, noS6A_Law3967, noS6A_Law3968, noS6A_Law3969, noS6A_Law3970⟩

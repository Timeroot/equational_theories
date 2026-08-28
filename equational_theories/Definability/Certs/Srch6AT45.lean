import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 46 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `40`
equations here, 2,369 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4011 takes them (118 nodes). -/
def ordS6A_Law4011 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4011. -/
theorem noS6A_Law4011 : ∀ v : Magma.tupS6A,
    ¬ @Equation4011 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4011) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4011) (by native_decide) v.1 v.2
    ((@Law4011.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4012 takes them (79 nodes). -/
def ordS6A_Law4012 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4012. -/
theorem noS6A_Law4012 : ∀ v : Magma.tupS6A,
    ¬ @Equation4012 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4012) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4012) (by native_decide) v.1 v.2
    ((@Law4012.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4013 takes them (168 nodes). -/
def ordS6A_Law4013 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4013. -/
theorem noS6A_Law4013 : ∀ v : Magma.tupS6A,
    ¬ @Equation4013 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4013) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4013) (by native_decide) v.1 v.2
    ((@Law4013.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4014 takes them (134 nodes). -/
def ordS6A_Law4014 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4014. -/
theorem noS6A_Law4014 : ∀ v : Magma.tupS6A,
    ¬ @Equation4014 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4014) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4014) (by native_decide) v.1 v.2
    ((@Law4014.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4015 takes them (70 nodes). -/
def ordS6A_Law4015 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4015. -/
theorem noS6A_Law4015 : ∀ v : Magma.tupS6A,
    ¬ @Equation4015 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4015) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4015) (by native_decide) v.1 v.2
    ((@Law4015.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4016 takes them (49 nodes). -/
def ordS6A_Law4016 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4016. -/
theorem noS6A_Law4016 : ∀ v : Magma.tupS6A,
    ¬ @Equation4016 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4016) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4016) (by native_decide) v.1 v.2
    ((@Law4016.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4017 takes them (68 nodes). -/
def ordS6A_Law4017 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4017. -/
theorem noS6A_Law4017 : ∀ v : Magma.tupS6A,
    ¬ @Equation4017 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4017) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4017) (by native_decide) v.1 v.2
    ((@Law4017.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4018 takes them (127 nodes). -/
def ordS6A_Law4018 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4018. -/
theorem noS6A_Law4018 : ∀ v : Magma.tupS6A,
    ¬ @Equation4018 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4018) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4018) (by native_decide) v.1 v.2
    ((@Law4018.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4019 takes them (63 nodes). -/
def ordS6A_Law4019 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4019. -/
theorem noS6A_Law4019 : ∀ v : Magma.tupS6A,
    ¬ @Equation4019 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4019) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4019) (by native_decide) v.1 v.2
    ((@Law4019.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4020 takes them (55 nodes). -/
def ordS6A_Law4020 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4020. -/
theorem noS6A_Law4020 : ∀ v : Magma.tupS6A,
    ¬ @Equation4020 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4020) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4020) (by native_decide) v.1 v.2
    ((@Law4020.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4021 takes them (42 nodes). -/
def ordS6A_Law4021 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4021. -/
theorem noS6A_Law4021 : ∀ v : Magma.tupS6A,
    ¬ @Equation4021 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4021) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4021) (by native_decide) v.1 v.2
    ((@Law4021.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4022 takes them (34 nodes). -/
def ordS6A_Law4022 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4022. -/
theorem noS6A_Law4022 : ∀ v : Magma.tupS6A,
    ¬ @Equation4022 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4022) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4022) (by native_decide) v.1 v.2
    ((@Law4022.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4024 takes them (34 nodes). -/
def ordS6A_Law4024 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4024. -/
theorem noS6A_Law4024 : ∀ v : Magma.tupS6A,
    ¬ @Equation4024 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4024) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4024) (by native_decide) v.1 v.2
    ((@Law4024.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4025 takes them (34 nodes). -/
def ordS6A_Law4025 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4025. -/
theorem noS6A_Law4025 : ∀ v : Magma.tupS6A,
    ¬ @Equation4025 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4025) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4025) (by native_decide) v.1 v.2
    ((@Law4025.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4026 takes them (105 nodes). -/
def ordS6A_Law4026 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4026. -/
theorem noS6A_Law4026 : ∀ v : Magma.tupS6A,
    ¬ @Equation4026 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4026) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4026) (by native_decide) v.1 v.2
    ((@Law4026.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4027 takes them (103 nodes). -/
def ordS6A_Law4027 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4027. -/
theorem noS6A_Law4027 : ∀ v : Magma.tupS6A,
    ¬ @Equation4027 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4027) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4027) (by native_decide) v.1 v.2
    ((@Law4027.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4028 takes them (48 nodes). -/
def ordS6A_Law4028 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4028. -/
theorem noS6A_Law4028 : ∀ v : Magma.tupS6A,
    ¬ @Equation4028 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4028) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4028) (by native_decide) v.1 v.2
    ((@Law4028.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4029 takes them (35 nodes). -/
def ordS6A_Law4029 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4029. -/
theorem noS6A_Law4029 : ∀ v : Magma.tupS6A,
    ¬ @Equation4029 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4029) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4029) (by native_decide) v.1 v.2
    ((@Law4029.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4030 takes them (54 nodes). -/
def ordS6A_Law4030 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4030. -/
theorem noS6A_Law4030 : ∀ v : Magma.tupS6A,
    ¬ @Equation4030 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4030) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4030) (by native_decide) v.1 v.2
    ((@Law4030.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4031 takes them (99 nodes). -/
def ordS6A_Law4031 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4031. -/
theorem noS6A_Law4031 : ∀ v : Magma.tupS6A,
    ¬ @Equation4031 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4031) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4031) (by native_decide) v.1 v.2
    ((@Law4031.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4032 takes them (52 nodes). -/
def ordS6A_Law4032 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4032. -/
theorem noS6A_Law4032 : ∀ v : Magma.tupS6A,
    ¬ @Equation4032 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4032) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4032) (by native_decide) v.1 v.2
    ((@Law4032.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4033 takes them (52 nodes). -/
def ordS6A_Law4033 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4033. -/
theorem noS6A_Law4033 : ∀ v : Magma.tupS6A,
    ¬ @Equation4033 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4033) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4033) (by native_decide) v.1 v.2
    ((@Law4033.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4034 takes them (32 nodes). -/
def ordS6A_Law4034 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4034. -/
theorem noS6A_Law4034 : ∀ v : Magma.tupS6A,
    ¬ @Equation4034 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4034) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4034) (by native_decide) v.1 v.2
    ((@Law4034.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4035 takes them (77 nodes). -/
def ordS6A_Law4035 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4035. -/
theorem noS6A_Law4035 : ∀ v : Magma.tupS6A,
    ¬ @Equation4035 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4035) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4035) (by native_decide) v.1 v.2
    ((@Law4035.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4036 takes them (30 nodes). -/
def ordS6A_Law4036 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4036. -/
theorem noS6A_Law4036 : ∀ v : Magma.tupS6A,
    ¬ @Equation4036 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4036) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4036) (by native_decide) v.1 v.2
    ((@Law4036.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4037 takes them (30 nodes). -/
def ordS6A_Law4037 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4037. -/
theorem noS6A_Law4037 : ∀ v : Magma.tupS6A,
    ¬ @Equation4037 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4037) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4037) (by native_decide) v.1 v.2
    ((@Law4037.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4038 takes them (30 nodes). -/
def ordS6A_Law4038 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4038. -/
theorem noS6A_Law4038 : ∀ v : Magma.tupS6A,
    ¬ @Equation4038 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4038) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4038) (by native_decide) v.1 v.2
    ((@Law4038.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4039 takes them (27 nodes). -/
def ordS6A_Law4039 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4039. -/
theorem noS6A_Law4039 : ∀ v : Magma.tupS6A,
    ¬ @Equation4039 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4039) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4039) (by native_decide) v.1 v.2
    ((@Law4039.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4041 takes them (27 nodes). -/
def ordS6A_Law4041 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4041. -/
theorem noS6A_Law4041 : ∀ v : Magma.tupS6A,
    ¬ @Equation4041 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4041) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4041) (by native_decide) v.1 v.2
    ((@Law4041.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4042 takes them (27 nodes). -/
def ordS6A_Law4042 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4042. -/
theorem noS6A_Law4042 : ∀ v : Magma.tupS6A,
    ¬ @Equation4042 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4042) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4042) (by native_decide) v.1 v.2
    ((@Law4042.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4043 takes them (27 nodes). -/
def ordS6A_Law4043 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4043. -/
theorem noS6A_Law4043 : ∀ v : Magma.tupS6A,
    ¬ @Equation4043 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4043) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4043) (by native_decide) v.1 v.2
    ((@Law4043.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4044 takes them (48 nodes). -/
def ordS6A_Law4044 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4044. -/
theorem noS6A_Law4044 : ∀ v : Magma.tupS6A,
    ¬ @Equation4044 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4044) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4044) (by native_decide) v.1 v.2
    ((@Law4044.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4045 takes them (98 nodes). -/
def ordS6A_Law4045 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4045. -/
theorem noS6A_Law4045 : ∀ v : Magma.tupS6A,
    ¬ @Equation4045 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4045) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4045) (by native_decide) v.1 v.2
    ((@Law4045.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4046 takes them (43 nodes). -/
def ordS6A_Law4046 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4046. -/
theorem noS6A_Law4046 : ∀ v : Magma.tupS6A,
    ¬ @Equation4046 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4046) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4046) (by native_decide) v.1 v.2
    ((@Law4046.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4047 takes them (43 nodes). -/
def ordS6A_Law4047 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4047. -/
theorem noS6A_Law4047 : ∀ v : Magma.tupS6A,
    ¬ @Equation4047 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4047) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4047) (by native_decide) v.1 v.2
    ((@Law4047.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4048 takes them (30 nodes). -/
def ordS6A_Law4048 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4048. -/
theorem noS6A_Law4048 : ∀ v : Magma.tupS6A,
    ¬ @Equation4048 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4048) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4048) (by native_decide) v.1 v.2
    ((@Law4048.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4049 takes them (34 nodes). -/
def ordS6A_Law4049 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4049. -/
theorem noS6A_Law4049 : ∀ v : Magma.tupS6A,
    ¬ @Equation4049 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4049) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4049) (by native_decide) v.1 v.2
    ((@Law4049.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4050 takes them (79 nodes). -/
def ordS6A_Law4050 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4050. -/
theorem noS6A_Law4050 : ∀ v : Magma.tupS6A,
    ¬ @Equation4050 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4050) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4050) (by native_decide) v.1 v.2
    ((@Law4050.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4051 takes them (32 nodes). -/
def ordS6A_Law4051 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4051. -/
theorem noS6A_Law4051 : ∀ v : Magma.tupS6A,
    ¬ @Equation4051 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4051) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4051) (by native_decide) v.1 v.2
    ((@Law4051.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4052 takes them (32 nodes). -/
def ordS6A_Law4052 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4052. -/
theorem noS6A_Law4052 : ∀ v : Magma.tupS6A,
    ¬ @Equation4052 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4052) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4052) (by native_decide) v.1 v.2
    ((@Law4052.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `40` equations. -/
theorem srch6A_refutes_45 :
    FamilyRefutes Magma.srch6A [
      4011, 4012, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4024, 4025, 4026,
      4027, 4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4041, 4042,
      4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052
    ] :=
  ⟨noS6A_Law4011, noS6A_Law4012, noS6A_Law4013, noS6A_Law4014, noS6A_Law4015, noS6A_Law4016, noS6A_Law4017, noS6A_Law4018, noS6A_Law4019, noS6A_Law4020, noS6A_Law4021, noS6A_Law4022, noS6A_Law4024, noS6A_Law4025, noS6A_Law4026, noS6A_Law4027, noS6A_Law4028, noS6A_Law4029, noS6A_Law4030, noS6A_Law4031, noS6A_Law4032, noS6A_Law4033, noS6A_Law4034, noS6A_Law4035, noS6A_Law4036, noS6A_Law4037, noS6A_Law4038, noS6A_Law4039, noS6A_Law4041, noS6A_Law4042, noS6A_Law4043, noS6A_Law4044, noS6A_Law4045, noS6A_Law4046, noS6A_Law4047, noS6A_Law4048, noS6A_Law4049, noS6A_Law4050, noS6A_Law4051, noS6A_Law4052⟩

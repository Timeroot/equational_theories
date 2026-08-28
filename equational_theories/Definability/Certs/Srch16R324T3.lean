import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate targets: `Magma.srch16R324` (part 4 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R324_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `52` equations here, 196 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3865 takes them (5 nodes). -/
def ordS16R324_Law3865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3865. -/
theorem noS16R324_Law3865 : ∀ v : Magma.tup16R324,
    ¬ @Equation3865 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3868 takes them (3 nodes). -/
def ordS16R324_Law3868 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3868. -/
theorem noS16R324_Law3868 : ∀ v : Magma.tup16R324,
    ¬ @Equation3868 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (3 nodes). -/
def ordS16R324_Law3871 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3871. -/
theorem noS16R324_Law3871 : ∀ v : Magma.tup16R324,
    ¬ @Equation3871 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3878 takes them (4 nodes). -/
def ordS16R324_Law3878 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3878. -/
theorem noS16R324_Law3878 : ∀ v : Magma.tup16R324,
    ¬ @Equation3878 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3878) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3878) (by native_decide) v.1 v.2
    ((@Law3878.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (5 nodes). -/
def ordS16R324_Law3880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3880. -/
theorem noS16R324_Law3880 : ∀ v : Magma.tup16R324,
    ¬ @Equation3880 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (3 nodes). -/
def ordS16R324_Law3887 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3887. -/
theorem noS16R324_Law3887 : ∀ v : Magma.tup16R324,
    ¬ @Equation3887 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (5 nodes). -/
def ordS16R324_Law3917 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3917. -/
theorem noS16R324_Law3917 : ∀ v : Magma.tup16R324,
    ¬ @Equation3917 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (3 nodes). -/
def ordS16R324_Law3924 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3924. -/
theorem noS16R324_Law3924 : ∀ v : Magma.tup16R324,
    ¬ @Equation3924 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3951 takes them (4 nodes). -/
def ordS16R324_Law3951 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3951. -/
theorem noS16R324_Law3951 : ∀ v : Magma.tup16R324,
    ¬ @Equation3951 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3951) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3951) (by native_decide) v.1 v.2
    ((@Law3951.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (5 nodes). -/
def ordS16R324_Law3955 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3955. -/
theorem noS16R324_Law3955 : ∀ v : Magma.tup16R324,
    ¬ @Equation3955 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (3 nodes). -/
def ordS16R324_Law3962 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3962. -/
theorem noS16R324_Law3962 : ∀ v : Magma.tup16R324,
    ¬ @Equation3962 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (5 nodes). -/
def ordS16R324_Law3997 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3997. -/
theorem noS16R324_Law3997 : ∀ v : Magma.tup16R324,
    ¬ @Equation3997 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (3 nodes). -/
def ordS16R324_Law4023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4023. -/
theorem noS16R324_Law4023 : ∀ v : Magma.tup16R324,
    ¬ @Equation4023 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (3 nodes). -/
def ordS16R324_Law4068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4068. -/
theorem noS16R324_Law4068 : ∀ v : Magma.tup16R324,
    ¬ @Equation4068 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4071 takes them (3 nodes). -/
def ordS16R324_Law4071 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4071. -/
theorem noS16R324_Law4071 : ∀ v : Magma.tup16R324,
    ¬ @Equation4071 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4073 takes them (4 nodes). -/
def ordS16R324_Law4073 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4073. -/
theorem noS16R324_Law4073 : ∀ v : Magma.tup16R324,
    ¬ @Equation4073 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4073) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4073) (by native_decide) v.1 v.2
    ((@Law4073.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (5 nodes). -/
def ordS16R324_Law4074 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4074. -/
theorem noS16R324_Law4074 : ∀ v : Magma.tup16R324,
    ¬ @Equation4074 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (5 nodes). -/
def ordS16R324_Law4083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4083. -/
theorem noS16R324_Law4083 : ∀ v : Magma.tup16R324,
    ¬ @Equation4083 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4091 takes them (4 nodes). -/
def ordS16R324_Law4091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4091. -/
theorem noS16R324_Law4091 : ∀ v : Magma.tup16R324,
    ¬ @Equation4091 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4091) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4091) (by native_decide) v.1 v.2
    ((@Law4091.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4127 takes them (3 nodes). -/
def ordS16R324_Law4127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4127. -/
theorem noS16R324_Law4127 : ∀ v : Magma.tup16R324,
    ¬ @Equation4127 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (5 nodes). -/
def ordS16R324_Law4130 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4130. -/
theorem noS16R324_Law4130 : ∀ v : Magma.tup16R324,
    ¬ @Equation4130 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4131 takes them (4 nodes). -/
def ordS16R324_Law4131 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4131. -/
theorem noS16R324_Law4131 : ∀ v : Magma.tup16R324,
    ¬ @Equation4131 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4131) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4131) (by native_decide) v.1 v.2
    ((@Law4131.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (3 nodes). -/
def ordS16R324_Law4135 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4135. -/
theorem noS16R324_Law4135 : ∀ v : Magma.tup16R324,
    ¬ @Equation4135 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (4 nodes). -/
def ordS16R324_Law4146 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4146. -/
theorem noS16R324_Law4146 : ∀ v : Magma.tup16R324,
    ¬ @Equation4146 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (5 nodes). -/
def ordS16R324_Law4158 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4158. -/
theorem noS16R324_Law4158 : ∀ v : Magma.tup16R324,
    ¬ @Equation4158 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4164 takes them (4 nodes). -/
def ordS16R324_Law4164 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4164. -/
theorem noS16R324_Law4164 : ∀ v : Magma.tup16R324,
    ¬ @Equation4164 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4164) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4164) (by native_decide) v.1 v.2
    ((@Law4164.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (5 nodes). -/
def ordS16R324_Law4200 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4200. -/
theorem noS16R324_Law4200 : ∀ v : Magma.tup16R324,
    ¬ @Equation4200 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4273 takes them (4 nodes). -/
def ordS16R324_Law4273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4273. -/
theorem noS16R324_Law4273 : ∀ v : Magma.tup16R324,
    ¬ @Equation4273 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4273) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4273) (by native_decide) v.1 v.2
    ((@Law4273.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (3 nodes). -/
def ordS16R324_Law4275 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4275. -/
theorem noS16R324_Law4275 : ∀ v : Magma.tup16R324,
    ¬ @Equation4275 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (3 nodes). -/
def ordS16R324_Law4283 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4283. -/
theorem noS16R324_Law4283 : ∀ v : Magma.tup16R324,
    ¬ @Equation4283 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4290 takes them (4 nodes). -/
def ordS16R324_Law4290 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4290. -/
theorem noS16R324_Law4290 : ∀ v : Magma.tup16R324,
    ¬ @Equation4290 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4290) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4290) (by native_decide) v.1 v.2
    ((@Law4290.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (3 nodes). -/
def ordS16R324_Law4307 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4307. -/
theorem noS16R324_Law4307 : ∀ v : Magma.tup16R324,
    ¬ @Equation4307 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4332 takes them (4 nodes). -/
def ordS16R324_Law4332 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4332. -/
theorem noS16R324_Law4332 : ∀ v : Magma.tup16R324,
    ¬ @Equation4332 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4332) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4332) (by native_decide) v.1 v.2
    ((@Law4332.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (3 nodes). -/
def ordS16R324_Law4358 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4358. -/
theorem noS16R324_Law4358 : ∀ v : Magma.tup16R324,
    ¬ @Equation4358 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4369 takes them (4 nodes). -/
def ordS16R324_Law4369 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4369. -/
theorem noS16R324_Law4369 : ∀ v : Magma.tup16R324,
    ¬ @Equation4369 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4369) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4369) (by native_decide) v.1 v.2
    ((@Law4369.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (3 nodes). -/
def ordS16R324_Law4383 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4383. -/
theorem noS16R324_Law4383 : ∀ v : Magma.tup16R324,
    ¬ @Equation4383 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4386 takes them (4 nodes). -/
def ordS16R324_Law4386 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4386. -/
theorem noS16R324_Law4386 : ∀ v : Magma.tup16R324,
    ¬ @Equation4386 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4386) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4386) (by native_decide) v.1 v.2
    ((@Law4386.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4398 takes them (3 nodes). -/
def ordS16R324_Law4398 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4398. -/
theorem noS16R324_Law4398 : ∀ v : Magma.tup16R324,
    ¬ @Equation4398 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4408 takes them (4 nodes). -/
def ordS16R324_Law4408 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4408. -/
theorem noS16R324_Law4408 : ∀ v : Magma.tup16R324,
    ¬ @Equation4408 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4408) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4408) (by native_decide) v.1 v.2
    ((@Law4408.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4409 takes them (3 nodes). -/
def ordS16R324_Law4409 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4409. -/
theorem noS16R324_Law4409 : ∀ v : Magma.tup16R324,
    ¬ @Equation4409 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4442 takes them (3 nodes). -/
def ordS16R324_Law4442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4442. -/
theorem noS16R324_Law4442 : ∀ v : Magma.tup16R324,
    ¬ @Equation4442 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4442) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4442) (by native_decide) v.1 v.2
    ((@Law4442.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4446 takes them (4 nodes). -/
def ordS16R324_Law4446 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4446. -/
theorem noS16R324_Law4446 : ∀ v : Magma.tup16R324,
    ¬ @Equation4446 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4446) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4446) (by native_decide) v.1 v.2
    ((@Law4446.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4458 takes them (4 nodes). -/
def ordS16R324_Law4458 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4458. -/
theorem noS16R324_Law4458 : ∀ v : Magma.tup16R324,
    ¬ @Equation4458 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4458) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4458) (by native_decide) v.1 v.2
    ((@Law4458.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4479 takes them (4 nodes). -/
def ordS16R324_Law4479 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4479. -/
theorem noS16R324_Law4479 : ∀ v : Magma.tup16R324,
    ¬ @Equation4479 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4479) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4479) (by native_decide) v.1 v.2
    ((@Law4479.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (3 nodes). -/
def ordS16R324_Law4585 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4585. -/
theorem noS16R324_Law4585 : ∀ v : Magma.tup16R324,
    ¬ @Equation4585 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4588 takes them (4 nodes). -/
def ordS16R324_Law4588 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4588. -/
theorem noS16R324_Law4588 : ∀ v : Magma.tup16R324,
    ¬ @Equation4588 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4588) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4588) (by native_decide) v.1 v.2
    ((@Law4588.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4605 takes them (4 nodes). -/
def ordS16R324_Law4605 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4605. -/
theorem noS16R324_Law4605 : ∀ v : Magma.tup16R324,
    ¬ @Equation4605 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4605) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4605) (by native_decide) v.1 v.2
    ((@Law4605.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (3 nodes). -/
def ordS16R324_Law4635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4635. -/
theorem noS16R324_Law4635 : ∀ v : Magma.tup16R324,
    ¬ @Equation4635 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4647 takes them (4 nodes). -/
def ordS16R324_Law4647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4647. -/
theorem noS16R324_Law4647 : ∀ v : Magma.tup16R324,
    ¬ @Equation4647 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4647) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4647) (by native_decide) v.1 v.2
    ((@Law4647.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (3 nodes). -/
def ordS16R324_Law4656 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4656. -/
theorem noS16R324_Law4656 : ∀ v : Magma.tup16R324,
    ¬ @Equation4656 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (3 nodes). -/
def ordS16R324_Law4677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4677. -/
theorem noS16R324_Law4677 : ∀ v : Magma.tup16R324,
    ¬ @Equation4677 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4684 takes them (4 nodes). -/
def ordS16R324_Law4684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4684. -/
theorem noS16R324_Law4684 : ∀ v : Magma.tup16R324,
    ¬ @Equation4684 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4684) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law4684) (by native_decide) v.1 v.2
    ((@Law4684.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- No member of the class satisfies any of these `52` equations. -/
theorem srch16R324_refutes_3 :
    FamilyRefutes Magma.srch16R324 [
      3865, 3868, 3871, 3878, 3880, 3887, 3917, 3924, 3951, 3955, 3962, 3997, 4023, 4068, 4071,
      4073, 4074, 4083, 4091, 4127, 4130, 4131, 4135, 4146, 4158, 4164, 4200, 4273, 4275, 4283,
      4290, 4307, 4332, 4358, 4369, 4383, 4386, 4398, 4408, 4409, 4442, 4446, 4458, 4479, 4585,
      4588, 4605, 4635, 4647, 4656, 4677, 4684
    ] :=
  ⟨noS16R324_Law3865, noS16R324_Law3868, noS16R324_Law3871, noS16R324_Law3878, noS16R324_Law3880, noS16R324_Law3887, noS16R324_Law3917, noS16R324_Law3924, noS16R324_Law3951, noS16R324_Law3955, noS16R324_Law3962, noS16R324_Law3997, noS16R324_Law4023, noS16R324_Law4068, noS16R324_Law4071, noS16R324_Law4073, noS16R324_Law4074, noS16R324_Law4083, noS16R324_Law4091, noS16R324_Law4127, noS16R324_Law4130, noS16R324_Law4131, noS16R324_Law4135, noS16R324_Law4146, noS16R324_Law4158, noS16R324_Law4164, noS16R324_Law4200, noS16R324_Law4273, noS16R324_Law4275, noS16R324_Law4283, noS16R324_Law4290, noS16R324_Law4307, noS16R324_Law4332, noS16R324_Law4358, noS16R324_Law4369, noS16R324_Law4383, noS16R324_Law4386, noS16R324_Law4398, noS16R324_Law4408, noS16R324_Law4409, noS16R324_Law4442, noS16R324_Law4446, noS16R324_Law4458, noS16R324_Law4479, noS16R324_Law4585, noS16R324_Law4588, noS16R324_Law4605, noS16R324_Law4635, noS16R324_Law4647, noS16R324_Law4656, noS16R324_Law4677, noS16R324_Law4684⟩

import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 12 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `78` equations here, 834 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4061 takes them (6 nodes). -/
def ordS8R164_Law4061 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4061. -/
theorem noS8R164_Law4061 : ∀ v : Magma.tup8R164,
    ¬ @Equation4061 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4061) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4061) (by native_decide) v.1 v.2
    ((@Law4061.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4062 takes them (6 nodes). -/
def ordS8R164_Law4062 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4062. -/
theorem noS8R164_Law4062 : ∀ v : Magma.tup8R164,
    ¬ @Equation4062 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4062) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4062) (by native_decide) v.1 v.2
    ((@Law4062.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4063 takes them (6 nodes). -/
def ordS8R164_Law4063 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4063. -/
theorem noS8R164_Law4063 : ∀ v : Magma.tup8R164,
    ¬ @Equation4063 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4063) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4063) (by native_decide) v.1 v.2
    ((@Law4063.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4064 takes them (6 nodes). -/
def ordS8R164_Law4064 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4064. -/
theorem noS8R164_Law4064 : ∀ v : Magma.tup8R164,
    ¬ @Equation4064 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4064) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law4064) (by native_decide) v.1 v.2
    ((@Law4064.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4070 takes them (25 nodes). -/
def ordS8R164_Law4070 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4070. -/
theorem noS8R164_Law4070 : ∀ v : Magma.tup8R164,
    ¬ @Equation4070 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4070) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4070) (by native_decide) v.1 v.2
    ((@Law4070.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4072 takes them (13 nodes). -/
def ordS8R164_Law4072 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4072. -/
theorem noS8R164_Law4072 : ∀ v : Magma.tup8R164,
    ¬ @Equation4072 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4072) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4072) (by native_decide) v.1 v.2
    ((@Law4072.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (13 nodes). -/
def ordS8R164_Law4074 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4074. -/
theorem noS8R164_Law4074 : ∀ v : Magma.tup8R164,
    ¬ @Equation4074 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4075 takes them (10 nodes). -/
def ordS8R164_Law4075 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4075. -/
theorem noS8R164_Law4075 : ∀ v : Magma.tup8R164,
    ¬ @Equation4075 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4075) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4075) (by native_decide) v.1 v.2
    ((@Law4075.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4076 takes them (18 nodes). -/
def ordS8R164_Law4076 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4076. -/
theorem noS8R164_Law4076 : ∀ v : Magma.tup8R164,
    ¬ @Equation4076 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4076) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4076) (by native_decide) v.1 v.2
    ((@Law4076.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4077 takes them (10 nodes). -/
def ordS8R164_Law4077 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4077. -/
theorem noS8R164_Law4077 : ∀ v : Magma.tup8R164,
    ¬ @Equation4077 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4077) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4077) (by native_decide) v.1 v.2
    ((@Law4077.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4078 takes them (12 nodes). -/
def ordS8R164_Law4078 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4078. -/
theorem noS8R164_Law4078 : ∀ v : Magma.tup8R164,
    ¬ @Equation4078 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4078) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4078) (by native_decide) v.1 v.2
    ((@Law4078.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4079 takes them (9 nodes). -/
def ordS8R164_Law4079 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4079. -/
theorem noS8R164_Law4079 : ∀ v : Magma.tup8R164,
    ¬ @Equation4079 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4079) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4079) (by native_decide) v.1 v.2
    ((@Law4079.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4080 takes them (12 nodes). -/
def ordS8R164_Law4080 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4080. -/
theorem noS8R164_Law4080 : ∀ v : Magma.tup8R164,
    ¬ @Equation4080 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4080) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4080) (by native_decide) v.1 v.2
    ((@Law4080.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4082 takes them (7 nodes). -/
def ordS8R164_Law4082 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4082. -/
theorem noS8R164_Law4082 : ∀ v : Magma.tup8R164,
    ¬ @Equation4082 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4082) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4082) (by native_decide) v.1 v.2
    ((@Law4082.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4084 takes them (19 nodes). -/
def ordS8R164_Law4084 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4084. -/
theorem noS8R164_Law4084 : ∀ v : Magma.tup8R164,
    ¬ @Equation4084 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4084) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4084) (by native_decide) v.1 v.2
    ((@Law4084.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4085 takes them (11 nodes). -/
def ordS8R164_Law4085 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4085. -/
theorem noS8R164_Law4085 : ∀ v : Magma.tup8R164,
    ¬ @Equation4085 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4085) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4085) (by native_decide) v.1 v.2
    ((@Law4085.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4086 takes them (10 nodes). -/
def ordS8R164_Law4086 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4086. -/
theorem noS8R164_Law4086 : ∀ v : Magma.tup8R164,
    ¬ @Equation4086 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4086) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4086) (by native_decide) v.1 v.2
    ((@Law4086.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4087 takes them (12 nodes). -/
def ordS8R164_Law4087 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4087. -/
theorem noS8R164_Law4087 : ∀ v : Magma.tup8R164,
    ¬ @Equation4087 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4087) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4087) (by native_decide) v.1 v.2
    ((@Law4087.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4088 takes them (9 nodes). -/
def ordS8R164_Law4088 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4088. -/
theorem noS8R164_Law4088 : ∀ v : Magma.tup8R164,
    ¬ @Equation4088 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4088) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4088) (by native_decide) v.1 v.2
    ((@Law4088.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4089 takes them (6 nodes). -/
def ordS8R164_Law4089 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4089. -/
theorem noS8R164_Law4089 : ∀ v : Magma.tup8R164,
    ¬ @Equation4089 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4089) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4089) (by native_decide) v.1 v.2
    ((@Law4089.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4100 takes them (12 nodes). -/
def ordS8R164_Law4100 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4100. -/
theorem noS8R164_Law4100 : ∀ v : Magma.tup8R164,
    ¬ @Equation4100 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4100) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4100) (by native_decide) v.1 v.2
    ((@Law4100.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4101 takes them (12 nodes). -/
def ordS8R164_Law4101 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4101. -/
theorem noS8R164_Law4101 : ∀ v : Magma.tup8R164,
    ¬ @Equation4101 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4101) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4101) (by native_decide) v.1 v.2
    ((@Law4101.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4102 takes them (7 nodes). -/
def ordS8R164_Law4102 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4102. -/
theorem noS8R164_Law4102 : ∀ v : Magma.tup8R164,
    ¬ @Equation4102 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4102) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4102) (by native_decide) v.1 v.2
    ((@Law4102.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4103 takes them (6 nodes). -/
def ordS8R164_Law4103 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4103. -/
theorem noS8R164_Law4103 : ∀ v : Magma.tup8R164,
    ¬ @Equation4103 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4103) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4103) (by native_decide) v.1 v.2
    ((@Law4103.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (15 nodes). -/
def ordS8R164_Law4104 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4104. -/
theorem noS8R164_Law4104 : ∀ v : Magma.tup8R164,
    ¬ @Equation4104 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4105 takes them (18 nodes). -/
def ordS8R164_Law4105 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4105. -/
theorem noS8R164_Law4105 : ∀ v : Magma.tup8R164,
    ¬ @Equation4105 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4105) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4105) (by native_decide) v.1 v.2
    ((@Law4105.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4107 takes them (11 nodes). -/
def ordS8R164_Law4107 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4107. -/
theorem noS8R164_Law4107 : ∀ v : Magma.tup8R164,
    ¬ @Equation4107 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4107) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4107) (by native_decide) v.1 v.2
    ((@Law4107.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4108 takes them (11 nodes). -/
def ordS8R164_Law4108 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4108. -/
theorem noS8R164_Law4108 : ∀ v : Magma.tup8R164,
    ¬ @Equation4108 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4108) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4108) (by native_decide) v.1 v.2
    ((@Law4108.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4110 takes them (9 nodes). -/
def ordS8R164_Law4110 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4110. -/
theorem noS8R164_Law4110 : ∀ v : Magma.tup8R164,
    ¬ @Equation4110 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4110) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4110) (by native_decide) v.1 v.2
    ((@Law4110.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4111 takes them (7 nodes). -/
def ordS8R164_Law4111 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4111. -/
theorem noS8R164_Law4111 : ∀ v : Magma.tup8R164,
    ¬ @Equation4111 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4111) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4111) (by native_decide) v.1 v.2
    ((@Law4111.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4112 takes them (10 nodes). -/
def ordS8R164_Law4112 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4112. -/
theorem noS8R164_Law4112 : ∀ v : Magma.tup8R164,
    ¬ @Equation4112 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4112) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4112) (by native_decide) v.1 v.2
    ((@Law4112.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4113 takes them (12 nodes). -/
def ordS8R164_Law4113 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4113. -/
theorem noS8R164_Law4113 : ∀ v : Magma.tup8R164,
    ¬ @Equation4113 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4113) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4113) (by native_decide) v.1 v.2
    ((@Law4113.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4114 takes them (7 nodes). -/
def ordS8R164_Law4114 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4114. -/
theorem noS8R164_Law4114 : ∀ v : Magma.tup8R164,
    ¬ @Equation4114 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4114) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4114) (by native_decide) v.1 v.2
    ((@Law4114.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4115 takes them (9 nodes). -/
def ordS8R164_Law4115 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4115. -/
theorem noS8R164_Law4115 : ∀ v : Magma.tup8R164,
    ¬ @Equation4115 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4115) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4115) (by native_decide) v.1 v.2
    ((@Law4115.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4116 takes them (6 nodes). -/
def ordS8R164_Law4116 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4116. -/
theorem noS8R164_Law4116 : ∀ v : Magma.tup8R164,
    ¬ @Equation4116 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4116) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4116) (by native_decide) v.1 v.2
    ((@Law4116.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4117 takes them (9 nodes). -/
def ordS8R164_Law4117 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4117. -/
theorem noS8R164_Law4117 : ∀ v : Magma.tup8R164,
    ¬ @Equation4117 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4117) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4117) (by native_decide) v.1 v.2
    ((@Law4117.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4119 takes them (9 nodes). -/
def ordS8R164_Law4119 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4119. -/
theorem noS8R164_Law4119 : ∀ v : Magma.tup8R164,
    ¬ @Equation4119 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4119) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4119) (by native_decide) v.1 v.2
    ((@Law4119.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4121 takes them (24 nodes). -/
def ordS8R164_Law4121 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4121. -/
theorem noS8R164_Law4121 : ∀ v : Magma.tup8R164,
    ¬ @Equation4121 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4121) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4121) (by native_decide) v.1 v.2
    ((@Law4121.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4122 takes them (9 nodes). -/
def ordS8R164_Law4122 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4122. -/
theorem noS8R164_Law4122 : ∀ v : Magma.tup8R164,
    ¬ @Equation4122 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4122) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4122) (by native_decide) v.1 v.2
    ((@Law4122.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4123 takes them (9 nodes). -/
def ordS8R164_Law4123 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4123. -/
theorem noS8R164_Law4123 : ∀ v : Magma.tup8R164,
    ¬ @Equation4123 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4123) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4123) (by native_decide) v.1 v.2
    ((@Law4123.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4124 takes them (13 nodes). -/
def ordS8R164_Law4124 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4124. -/
theorem noS8R164_Law4124 : ∀ v : Magma.tup8R164,
    ¬ @Equation4124 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4124) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4124) (by native_decide) v.1 v.2
    ((@Law4124.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4125 takes them (9 nodes). -/
def ordS8R164_Law4125 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4125. -/
theorem noS8R164_Law4125 : ∀ v : Magma.tup8R164,
    ¬ @Equation4125 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4125) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4125) (by native_decide) v.1 v.2
    ((@Law4125.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4126 takes them (9 nodes). -/
def ordS8R164_Law4126 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4126. -/
theorem noS8R164_Law4126 : ∀ v : Magma.tup8R164,
    ¬ @Equation4126 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4126) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4126) (by native_decide) v.1 v.2
    ((@Law4126.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4128 takes them (30 nodes). -/
def ordS8R164_Law4128 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4128. -/
theorem noS8R164_Law4128 : ∀ v : Magma.tup8R164,
    ¬ @Equation4128 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4128) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4128) (by native_decide) v.1 v.2
    ((@Law4128.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4129 takes them (9 nodes). -/
def ordS8R164_Law4129 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4129. -/
theorem noS8R164_Law4129 : ∀ v : Magma.tup8R164,
    ¬ @Equation4129 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4129) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4129) (by native_decide) v.1 v.2
    ((@Law4129.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (18 nodes). -/
def ordS8R164_Law4130 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4130. -/
theorem noS8R164_Law4130 : ∀ v : Magma.tup8R164,
    ¬ @Equation4130 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4132 takes them (9 nodes). -/
def ordS8R164_Law4132 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4132. -/
theorem noS8R164_Law4132 : ∀ v : Magma.tup8R164,
    ¬ @Equation4132 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4132) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4132) (by native_decide) v.1 v.2
    ((@Law4132.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4133 takes them (10 nodes). -/
def ordS8R164_Law4133 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4133. -/
theorem noS8R164_Law4133 : ∀ v : Magma.tup8R164,
    ¬ @Equation4133 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4133) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4133) (by native_decide) v.1 v.2
    ((@Law4133.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4134 takes them (13 nodes). -/
def ordS8R164_Law4134 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4134. -/
theorem noS8R164_Law4134 : ∀ v : Magma.tup8R164,
    ¬ @Equation4134 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4134) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4134) (by native_decide) v.1 v.2
    ((@Law4134.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4136 takes them (9 nodes). -/
def ordS8R164_Law4136 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4136. -/
theorem noS8R164_Law4136 : ∀ v : Magma.tup8R164,
    ¬ @Equation4136 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4136) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4136) (by native_decide) v.1 v.2
    ((@Law4136.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4137 takes them (9 nodes). -/
def ordS8R164_Law4137 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4137. -/
theorem noS8R164_Law4137 : ∀ v : Magma.tup8R164,
    ¬ @Equation4137 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4137) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4137) (by native_decide) v.1 v.2
    ((@Law4137.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4138 takes them (19 nodes). -/
def ordS8R164_Law4138 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4138. -/
theorem noS8R164_Law4138 : ∀ v : Magma.tup8R164,
    ¬ @Equation4138 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4138) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4138) (by native_decide) v.1 v.2
    ((@Law4138.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4139 takes them (9 nodes). -/
def ordS8R164_Law4139 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4139. -/
theorem noS8R164_Law4139 : ∀ v : Magma.tup8R164,
    ¬ @Equation4139 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4139) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4139) (by native_decide) v.1 v.2
    ((@Law4139.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4140 takes them (9 nodes). -/
def ordS8R164_Law4140 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4140. -/
theorem noS8R164_Law4140 : ∀ v : Magma.tup8R164,
    ¬ @Equation4140 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4140) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4140) (by native_decide) v.1 v.2
    ((@Law4140.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4141 takes them (10 nodes). -/
def ordS8R164_Law4141 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4141. -/
theorem noS8R164_Law4141 : ∀ v : Magma.tup8R164,
    ¬ @Equation4141 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4141) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4141) (by native_decide) v.1 v.2
    ((@Law4141.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4142 takes them (13 nodes). -/
def ordS8R164_Law4142 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4142. -/
theorem noS8R164_Law4142 : ∀ v : Magma.tup8R164,
    ¬ @Equation4142 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4142) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4142) (by native_decide) v.1 v.2
    ((@Law4142.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4144 takes them (9 nodes). -/
def ordS8R164_Law4144 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4144. -/
theorem noS8R164_Law4144 : ∀ v : Magma.tup8R164,
    ¬ @Equation4144 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4144) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4144) (by native_decide) v.1 v.2
    ((@Law4144.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4145 takes them (9 nodes). -/
def ordS8R164_Law4145 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4145. -/
theorem noS8R164_Law4145 : ∀ v : Magma.tup8R164,
    ¬ @Equation4145 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4145) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4145) (by native_decide) v.1 v.2
    ((@Law4145.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4147 takes them (9 nodes). -/
def ordS8R164_Law4147 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4147. -/
theorem noS8R164_Law4147 : ∀ v : Magma.tup8R164,
    ¬ @Equation4147 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4147) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4147) (by native_decide) v.1 v.2
    ((@Law4147.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4148 takes them (9 nodes). -/
def ordS8R164_Law4148 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4148. -/
theorem noS8R164_Law4148 : ∀ v : Magma.tup8R164,
    ¬ @Equation4148 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4148) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4148) (by native_decide) v.1 v.2
    ((@Law4148.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4149 takes them (9 nodes). -/
def ordS8R164_Law4149 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4149. -/
theorem noS8R164_Law4149 : ∀ v : Magma.tup8R164,
    ¬ @Equation4149 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4149) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4149) (by native_decide) v.1 v.2
    ((@Law4149.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4150 takes them (13 nodes). -/
def ordS8R164_Law4150 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4150. -/
theorem noS8R164_Law4150 : ∀ v : Magma.tup8R164,
    ¬ @Equation4150 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4150) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4150) (by native_decide) v.1 v.2
    ((@Law4150.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4151 takes them (9 nodes). -/
def ordS8R164_Law4151 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4151. -/
theorem noS8R164_Law4151 : ∀ v : Magma.tup8R164,
    ¬ @Equation4151 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4151) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4151) (by native_decide) v.1 v.2
    ((@Law4151.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4152 takes them (9 nodes). -/
def ordS8R164_Law4152 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4152. -/
theorem noS8R164_Law4152 : ∀ v : Magma.tup8R164,
    ¬ @Equation4152 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4152) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4152) (by native_decide) v.1 v.2
    ((@Law4152.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4153 takes them (9 nodes). -/
def ordS8R164_Law4153 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4153. -/
theorem noS8R164_Law4153 : ∀ v : Magma.tup8R164,
    ¬ @Equation4153 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4153) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4153) (by native_decide) v.1 v.2
    ((@Law4153.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4155 takes them (21 nodes). -/
def ordS8R164_Law4155 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4155. -/
theorem noS8R164_Law4155 : ∀ v : Magma.tup8R164,
    ¬ @Equation4155 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4155) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4155) (by native_decide) v.1 v.2
    ((@Law4155.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4156 takes them (6 nodes). -/
def ordS8R164_Law4156 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4156. -/
theorem noS8R164_Law4156 : ∀ v : Magma.tup8R164,
    ¬ @Equation4156 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4156) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4156) (by native_decide) v.1 v.2
    ((@Law4156.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4157 takes them (12 nodes). -/
def ordS8R164_Law4157 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4157. -/
theorem noS8R164_Law4157 : ∀ v : Magma.tup8R164,
    ¬ @Equation4157 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4157) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4157) (by native_decide) v.1 v.2
    ((@Law4157.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4159 takes them (6 nodes). -/
def ordS8R164_Law4159 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4159. -/
theorem noS8R164_Law4159 : ∀ v : Magma.tup8R164,
    ¬ @Equation4159 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4159) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4159) (by native_decide) v.1 v.2
    ((@Law4159.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4160 takes them (7 nodes). -/
def ordS8R164_Law4160 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4160. -/
theorem noS8R164_Law4160 : ∀ v : Magma.tup8R164,
    ¬ @Equation4160 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4160) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4160) (by native_decide) v.1 v.2
    ((@Law4160.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4161 takes them (10 nodes). -/
def ordS8R164_Law4161 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4161. -/
theorem noS8R164_Law4161 : ∀ v : Magma.tup8R164,
    ¬ @Equation4161 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4161) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4161) (by native_decide) v.1 v.2
    ((@Law4161.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4163 takes them (6 nodes). -/
def ordS8R164_Law4163 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4163. -/
theorem noS8R164_Law4163 : ∀ v : Magma.tup8R164,
    ¬ @Equation4163 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4163) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4163) (by native_decide) v.1 v.2
    ((@Law4163.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4164 takes them (12 nodes). -/
def ordS8R164_Law4164 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4164. -/
theorem noS8R164_Law4164 : ∀ v : Magma.tup8R164,
    ¬ @Equation4164 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4164) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4164) (by native_decide) v.1 v.2
    ((@Law4164.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4166 takes them (6 nodes). -/
def ordS8R164_Law4166 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4166. -/
theorem noS8R164_Law4166 : ∀ v : Magma.tup8R164,
    ¬ @Equation4166 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4166) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4166) (by native_decide) v.1 v.2
    ((@Law4166.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4168 takes them (10 nodes). -/
def ordS8R164_Law4168 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4168. -/
theorem noS8R164_Law4168 : ∀ v : Magma.tup8R164,
    ¬ @Equation4168 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4168) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4168) (by native_decide) v.1 v.2
    ((@Law4168.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4169 takes them (6 nodes). -/
def ordS8R164_Law4169 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4169. -/
theorem noS8R164_Law4169 : ∀ v : Magma.tup8R164,
    ¬ @Equation4169 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4169) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4169) (by native_decide) v.1 v.2
    ((@Law4169.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4170 takes them (7 nodes). -/
def ordS8R164_Law4170 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4170. -/
theorem noS8R164_Law4170 : ∀ v : Magma.tup8R164,
    ¬ @Equation4170 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4170) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4170) (by native_decide) v.1 v.2
    ((@Law4170.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4171 takes them (10 nodes). -/
def ordS8R164_Law4171 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4171. -/
theorem noS8R164_Law4171 : ∀ v : Magma.tup8R164,
    ¬ @Equation4171 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4171) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4171) (by native_decide) v.1 v.2
    ((@Law4171.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `78` equations. -/
theorem srch8R164_refutes_11 :
    FamilyRefutes Magma.srch8R164 [
      4061, 4062, 4063, 4064, 4070, 4072, 4074, 4075, 4076, 4077, 4078, 4079, 4080, 4082, 4084,
      4085, 4086, 4087, 4088, 4089, 4100, 4101, 4102, 4103, 4104, 4105, 4107, 4108, 4110, 4111,
      4112, 4113, 4114, 4115, 4116, 4117, 4119, 4121, 4122, 4123, 4124, 4125, 4126, 4128, 4129,
      4130, 4132, 4133, 4134, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4144, 4145, 4147, 4148,
      4149, 4150, 4151, 4152, 4153, 4155, 4156, 4157, 4159, 4160, 4161, 4163, 4164, 4166, 4168,
      4169, 4170, 4171
    ] :=
  ⟨noS8R164_Law4061, noS8R164_Law4062, noS8R164_Law4063, noS8R164_Law4064, noS8R164_Law4070, noS8R164_Law4072, noS8R164_Law4074, noS8R164_Law4075, noS8R164_Law4076, noS8R164_Law4077, noS8R164_Law4078, noS8R164_Law4079, noS8R164_Law4080, noS8R164_Law4082, noS8R164_Law4084, noS8R164_Law4085, noS8R164_Law4086, noS8R164_Law4087, noS8R164_Law4088, noS8R164_Law4089, noS8R164_Law4100, noS8R164_Law4101, noS8R164_Law4102, noS8R164_Law4103, noS8R164_Law4104, noS8R164_Law4105, noS8R164_Law4107, noS8R164_Law4108, noS8R164_Law4110, noS8R164_Law4111, noS8R164_Law4112, noS8R164_Law4113, noS8R164_Law4114, noS8R164_Law4115, noS8R164_Law4116, noS8R164_Law4117, noS8R164_Law4119, noS8R164_Law4121, noS8R164_Law4122, noS8R164_Law4123, noS8R164_Law4124, noS8R164_Law4125, noS8R164_Law4126, noS8R164_Law4128, noS8R164_Law4129, noS8R164_Law4130, noS8R164_Law4132, noS8R164_Law4133, noS8R164_Law4134, noS8R164_Law4136, noS8R164_Law4137, noS8R164_Law4138, noS8R164_Law4139, noS8R164_Law4140, noS8R164_Law4141, noS8R164_Law4142, noS8R164_Law4144, noS8R164_Law4145, noS8R164_Law4147, noS8R164_Law4148, noS8R164_Law4149, noS8R164_Law4150, noS8R164_Law4151, noS8R164_Law4152, noS8R164_Law4153, noS8R164_Law4155, noS8R164_Law4156, noS8R164_Law4157, noS8R164_Law4159, noS8R164_Law4160, noS8R164_Law4161, noS8R164_Law4163, noS8R164_Law4164, noS8R164_Law4166, noS8R164_Law4168, noS8R164_Law4169, noS8R164_Law4170, noS8R164_Law4171⟩

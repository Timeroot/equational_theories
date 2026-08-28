import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 47 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `25`
equations here, 2,934 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4053 takes them (32 nodes). -/
def ordS6A_Law4053 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4053. -/
theorem noS6A_Law4053 : ∀ v : Magma.tupS6A,
    ¬ @Equation4053 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4053) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4053) (by native_decide) v.1 v.2
    ((@Law4053.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4054 takes them (54 nodes). -/
def ordS6A_Law4054 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4054. -/
theorem noS6A_Law4054 : ∀ v : Magma.tupS6A,
    ¬ @Equation4054 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4054) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4054) (by native_decide) v.1 v.2
    ((@Law4054.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4055 takes them (99 nodes). -/
def ordS6A_Law4055 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4055. -/
theorem noS6A_Law4055 : ∀ v : Magma.tupS6A,
    ¬ @Equation4055 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4055) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4055) (by native_decide) v.1 v.2
    ((@Law4055.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4056 takes them (52 nodes). -/
def ordS6A_Law4056 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4056. -/
theorem noS6A_Law4056 : ∀ v : Magma.tupS6A,
    ¬ @Equation4056 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4056) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4056) (by native_decide) v.1 v.2
    ((@Law4056.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4057 takes them (52 nodes). -/
def ordS6A_Law4057 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4057. -/
theorem noS6A_Law4057 : ∀ v : Magma.tupS6A,
    ¬ @Equation4057 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4057) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4057) (by native_decide) v.1 v.2
    ((@Law4057.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4058 takes them (52 nodes). -/
def ordS6A_Law4058 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4058. -/
theorem noS6A_Law4058 : ∀ v : Magma.tupS6A,
    ¬ @Equation4058 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4058) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4058) (by native_decide) v.1 v.2
    ((@Law4058.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4059 takes them (27 nodes). -/
def ordS6A_Law4059 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4059. -/
theorem noS6A_Law4059 : ∀ v : Magma.tupS6A,
    ¬ @Equation4059 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4059) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4059) (by native_decide) v.1 v.2
    ((@Law4059.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4060 takes them (72 nodes). -/
def ordS6A_Law4060 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4060. -/
theorem noS6A_Law4060 : ∀ v : Magma.tupS6A,
    ¬ @Equation4060 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4060) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4060) (by native_decide) v.1 v.2
    ((@Law4060.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4061 takes them (25 nodes). -/
def ordS6A_Law4061 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4061. -/
theorem noS6A_Law4061 : ∀ v : Magma.tupS6A,
    ¬ @Equation4061 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4061) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4061) (by native_decide) v.1 v.2
    ((@Law4061.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4062 takes them (25 nodes). -/
def ordS6A_Law4062 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4062. -/
theorem noS6A_Law4062 : ∀ v : Magma.tupS6A,
    ¬ @Equation4062 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4062) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4062) (by native_decide) v.1 v.2
    ((@Law4062.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4063 takes them (25 nodes). -/
def ordS6A_Law4063 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4063. -/
theorem noS6A_Law4063 : ∀ v : Magma.tupS6A,
    ¬ @Equation4063 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4063) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4063) (by native_decide) v.1 v.2
    ((@Law4063.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4064 takes them (25 nodes). -/
def ordS6A_Law4064 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4064. -/
theorem noS6A_Law4064 : ∀ v : Magma.tupS6A,
    ¬ @Equation4064 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4064) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 6)
    (ord := ordS6A_Law4064) (by native_decide) v.1 v.2
    ((@Law4064.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4117 takes them (194 nodes). -/
def ordS6A_Law4117 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4117. -/
theorem noS6A_Law4117 : ∀ v : Magma.tupS6A,
    ¬ @Equation4117 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4117) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law4117) (by native_decide) v.1 v.2
    ((@Law4117.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4119 takes them (194 nodes). -/
def ordS6A_Law4119 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4119. -/
theorem noS6A_Law4119 : ∀ v : Magma.tupS6A,
    ¬ @Equation4119 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4119) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4119) (by native_decide) v.1 v.2
    ((@Law4119.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4122 takes them (179 nodes). -/
def ordS6A_Law4122 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4122. -/
theorem noS6A_Law4122 : ∀ v : Magma.tupS6A,
    ¬ @Equation4122 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4122) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4122) (by native_decide) v.1 v.2
    ((@Law4122.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4123 takes them (160 nodes). -/
def ordS6A_Law4123 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4123. -/
theorem noS6A_Law4123 : ∀ v : Magma.tupS6A,
    ¬ @Equation4123 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4123) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4123) (by native_decide) v.1 v.2
    ((@Law4123.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4124 takes them (336 nodes). -/
def ordS6A_Law4124 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4124. -/
theorem noS6A_Law4124 : ∀ v : Magma.tupS6A,
    ¬ @Equation4124 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4124) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4124) (by native_decide) v.1 v.2
    ((@Law4124.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4125 takes them (160 nodes). -/
def ordS6A_Law4125 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4125. -/
theorem noS6A_Law4125 : ∀ v : Magma.tupS6A,
    ¬ @Equation4125 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4125) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4125) (by native_decide) v.1 v.2
    ((@Law4125.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4126 takes them (160 nodes). -/
def ordS6A_Law4126 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4126. -/
theorem noS6A_Law4126 : ∀ v : Magma.tupS6A,
    ¬ @Equation4126 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4126) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4126) (by native_decide) v.1 v.2
    ((@Law4126.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4137 takes them (101 nodes). -/
def ordS6A_Law4137 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4137. -/
theorem noS6A_Law4137 : ∀ v : Magma.tupS6A,
    ¬ @Equation4137 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4137) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4137) (by native_decide) v.1 v.2
    ((@Law4137.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4139 takes them (94 nodes). -/
def ordS6A_Law4139 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4139. -/
theorem noS6A_Law4139 : ∀ v : Magma.tupS6A,
    ¬ @Equation4139 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4139) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4139) (by native_decide) v.1 v.2
    ((@Law4139.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4140 takes them (94 nodes). -/
def ordS6A_Law4140 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4140. -/
theorem noS6A_Law4140 : ∀ v : Magma.tupS6A,
    ¬ @Equation4140 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4140) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4140) (by native_decide) v.1 v.2
    ((@Law4140.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4141 takes them (157 nodes). -/
def ordS6A_Law4141 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4141. -/
theorem noS6A_Law4141 : ∀ v : Magma.tupS6A,
    ¬ @Equation4141 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4141) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4141) (by native_decide) v.1 v.2
    ((@Law4141.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4142 takes them (261 nodes). -/
def ordS6A_Law4142 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4142. -/
theorem noS6A_Law4142 : ∀ v : Magma.tupS6A,
    ¬ @Equation4142 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4142) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4142) (by native_decide) v.1 v.2
    ((@Law4142.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4143 takes them (304 nodes). -/
def ordS6A_Law4143 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4143. -/
theorem noS6A_Law4143 : ∀ v : Magma.tupS6A,
    ¬ @Equation4143 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch6A_refutes_46 :
    FamilyRefutes Magma.srch6A [
      4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063, 4064, 4117, 4119, 4122,
      4123, 4124, 4125, 4126, 4137, 4139, 4140, 4141, 4142, 4143
    ] :=
  ⟨noS6A_Law4053, noS6A_Law4054, noS6A_Law4055, noS6A_Law4056, noS6A_Law4057, noS6A_Law4058, noS6A_Law4059, noS6A_Law4060, noS6A_Law4061, noS6A_Law4062, noS6A_Law4063, noS6A_Law4064, noS6A_Law4117, noS6A_Law4119, noS6A_Law4122, noS6A_Law4123, noS6A_Law4124, noS6A_Law4125, noS6A_Law4126, noS6A_Law4137, noS6A_Law4139, noS6A_Law4140, noS6A_Law4141, noS6A_Law4142, noS6A_Law4143⟩

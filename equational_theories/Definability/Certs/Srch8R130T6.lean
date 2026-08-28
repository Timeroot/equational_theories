import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 7 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `72` equations here, 225 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4096 takes them (3 nodes). -/
def ordS8R130_Law4096 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4096. -/
theorem noS8R130_Law4096 : ∀ v : Magma.tup8R130,
    ¬ @Equation4096 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4096) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4096) (by native_decide) v.1 v.2
    ((@Law4096.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4100 takes them (3 nodes). -/
def ordS8R130_Law4100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4100. -/
theorem noS8R130_Law4100 : ∀ v : Magma.tup8R130,
    ¬ @Equation4100 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4100) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4100) (by native_decide) v.1 v.2
    ((@Law4100.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4120 takes them (3 nodes). -/
def ordS8R130_Law4120 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4120. -/
theorem noS8R130_Law4120 : ∀ v : Magma.tup8R130,
    ¬ @Equation4120 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4120) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4120) (by native_decide) v.1 v.2
    ((@Law4120.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4121 takes them (4 nodes). -/
def ordS8R130_Law4121 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4121. -/
theorem noS8R130_Law4121 : ∀ v : Magma.tup8R130,
    ¬ @Equation4121 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4121) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4121) (by native_decide) v.1 v.2
    ((@Law4121.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4127 takes them (3 nodes). -/
def ordS8R130_Law4127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4127. -/
theorem noS8R130_Law4127 : ∀ v : Magma.tup8R130,
    ¬ @Equation4127 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4128 takes them (4 nodes). -/
def ordS8R130_Law4128 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4128. -/
theorem noS8R130_Law4128 : ∀ v : Magma.tup8R130,
    ¬ @Equation4128 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4128) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4128) (by native_decide) v.1 v.2
    ((@Law4128.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (3 nodes). -/
def ordS8R130_Law4130 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4130. -/
theorem noS8R130_Law4130 : ∀ v : Magma.tup8R130,
    ¬ @Equation4130 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4131 takes them (4 nodes). -/
def ordS8R130_Law4131 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4131. -/
theorem noS8R130_Law4131 : ∀ v : Magma.tup8R130,
    ¬ @Equation4131 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4131) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4131) (by native_decide) v.1 v.2
    ((@Law4131.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (3 nodes). -/
def ordS8R130_Law4135 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4135. -/
theorem noS8R130_Law4135 : ∀ v : Magma.tup8R130,
    ¬ @Equation4135 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4143 takes them (3 nodes). -/
def ordS8R130_Law4143 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4143. -/
theorem noS8R130_Law4143 : ∀ v : Magma.tup8R130,
    ¬ @Equation4143 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (4 nodes). -/
def ordS8R130_Law4146 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4146. -/
theorem noS8R130_Law4146 : ∀ v : Magma.tup8R130,
    ¬ @Equation4146 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4155 takes them (3 nodes). -/
def ordS8R130_Law4155 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4155. -/
theorem noS8R130_Law4155 : ∀ v : Magma.tup8R130,
    ¬ @Equation4155 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4155) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4155) (by native_decide) v.1 v.2
    ((@Law4155.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (3 nodes). -/
def ordS8R130_Law4158 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4158. -/
theorem noS8R130_Law4158 : ∀ v : Magma.tup8R130,
    ¬ @Equation4158 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4165 takes them (3 nodes). -/
def ordS8R130_Law4165 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4165. -/
theorem noS8R130_Law4165 : ∀ v : Magma.tup8R130,
    ¬ @Equation4165 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4165) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4165) (by native_decide) v.1 v.2
    ((@Law4165.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4192 takes them (3 nodes). -/
def ordS8R130_Law4192 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4192. -/
theorem noS8R130_Law4192 : ∀ v : Magma.tup8R130,
    ¬ @Equation4192 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4192) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4192) (by native_decide) v.1 v.2
    ((@Law4192.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (3 nodes). -/
def ordS8R130_Law4200 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4200. -/
theorem noS8R130_Law4200 : ∀ v : Magma.tup8R130,
    ¬ @Equation4200 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4226 takes them (3 nodes). -/
def ordS8R130_Law4226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4226. -/
theorem noS8R130_Law4226 : ∀ v : Magma.tup8R130,
    ¬ @Equation4226 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4226) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4226) (by native_decide) v.1 v.2
    ((@Law4226.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4268 takes them (3 nodes). -/
def ordS8R130_Law4268 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4268. -/
theorem noS8R130_Law4268 : ∀ v : Magma.tup8R130,
    ¬ @Equation4268 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4268) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4268) (by native_decide) v.1 v.2
    ((@Law4268.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4270 takes them (3 nodes). -/
def ordS8R130_Law4270 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4270. -/
theorem noS8R130_Law4270 : ∀ v : Magma.tup8R130,
    ¬ @Equation4270 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4270) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4270) (by native_decide) v.1 v.2
    ((@Law4270.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4272 takes them (3 nodes). -/
def ordS8R130_Law4272 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4272. -/
theorem noS8R130_Law4272 : ∀ v : Magma.tup8R130,
    ¬ @Equation4272 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4272) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4272) (by native_decide) v.1 v.2
    ((@Law4272.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (3 nodes). -/
def ordS8R130_Law4275 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4275. -/
theorem noS8R130_Law4275 : ∀ v : Magma.tup8R130,
    ¬ @Equation4275 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4282 takes them (3 nodes). -/
def ordS8R130_Law4282 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4282. -/
theorem noS8R130_Law4282 : ∀ v : Magma.tup8R130,
    ¬ @Equation4282 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4282) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4282) (by native_decide) v.1 v.2
    ((@Law4282.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (3 nodes). -/
def ordS8R130_Law4283 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4283. -/
theorem noS8R130_Law4283 : ∀ v : Magma.tup8R130,
    ¬ @Equation4283 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4284 takes them (4 nodes). -/
def ordS8R130_Law4284 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4284. -/
theorem noS8R130_Law4284 : ∀ v : Magma.tup8R130,
    ¬ @Equation4284 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4284) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4284) (by native_decide) v.1 v.2
    ((@Law4284.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (3 nodes). -/
def ordS8R130_Law4291 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4291. -/
theorem noS8R130_Law4291 : ∀ v : Magma.tup8R130,
    ¬ @Equation4291 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (3 nodes). -/
def ordS8R130_Law4307 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4307. -/
theorem noS8R130_Law4307 : ∀ v : Magma.tup8R130,
    ¬ @Equation4307 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (3 nodes). -/
def ordS8R130_Law4314 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4314. -/
theorem noS8R130_Law4314 : ∀ v : Magma.tup8R130,
    ¬ @Equation4314 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4320 takes them (3 nodes). -/
def ordS8R130_Law4320 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4320. -/
theorem noS8R130_Law4320 : ∀ v : Magma.tup8R130,
    ¬ @Equation4320 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4320) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4320) (by native_decide) v.1 v.2
    ((@Law4320.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4341 takes them (3 nodes). -/
def ordS8R130_Law4341 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4341. -/
theorem noS8R130_Law4341 : ∀ v : Magma.tup8R130,
    ¬ @Equation4341 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4341) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4341) (by native_decide) v.1 v.2
    ((@Law4341.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4351 takes them (3 nodes). -/
def ordS8R130_Law4351 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4351. -/
theorem noS8R130_Law4351 : ∀ v : Magma.tup8R130,
    ¬ @Equation4351 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4351) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4351) (by native_decide) v.1 v.2
    ((@Law4351.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (3 nodes). -/
def ordS8R130_Law4358 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4358. -/
theorem noS8R130_Law4358 : ∀ v : Magma.tup8R130,
    ¬ @Equation4358 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (3 nodes). -/
def ordS8R130_Law4362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4362. -/
theorem noS8R130_Law4362 : ∀ v : Magma.tup8R130,
    ¬ @Equation4362 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4381 takes them (3 nodes). -/
def ordS8R130_Law4381 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4381. -/
theorem noS8R130_Law4381 : ∀ v : Magma.tup8R130,
    ¬ @Equation4381 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4381) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4381) (by native_decide) v.1 v.2
    ((@Law4381.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (3 nodes). -/
def ordS8R130_Law4383 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4383. -/
theorem noS8R130_Law4383 : ∀ v : Magma.tup8R130,
    ¬ @Equation4383 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4385 takes them (3 nodes). -/
def ordS8R130_Law4385 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4385. -/
theorem noS8R130_Law4385 : ∀ v : Magma.tup8R130,
    ¬ @Equation4385 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4385) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4385) (by native_decide) v.1 v.2
    ((@Law4385.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4388 takes them (3 nodes). -/
def ordS8R130_Law4388 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4388. -/
theorem noS8R130_Law4388 : ∀ v : Magma.tup8R130,
    ¬ @Equation4388 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4388) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4388) (by native_decide) v.1 v.2
    ((@Law4388.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4395 takes them (3 nodes). -/
def ordS8R130_Law4395 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4395. -/
theorem noS8R130_Law4395 : ∀ v : Magma.tup8R130,
    ¬ @Equation4395 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4395) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4395) (by native_decide) v.1 v.2
    ((@Law4395.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4396 takes them (4 nodes). -/
def ordS8R130_Law4396 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4396. -/
theorem noS8R130_Law4396 : ∀ v : Magma.tup8R130,
    ¬ @Equation4396 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4396) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4396) (by native_decide) v.1 v.2
    ((@Law4396.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4398 takes them (3 nodes). -/
def ordS8R130_Law4398 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4398. -/
theorem noS8R130_Law4398 : ∀ v : Magma.tup8R130,
    ¬ @Equation4398 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4406 takes them (3 nodes). -/
def ordS8R130_Law4406 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4406. -/
theorem noS8R130_Law4406 : ∀ v : Magma.tup8R130,
    ¬ @Equation4406 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4409 takes them (3 nodes). -/
def ordS8R130_Law4409 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4409. -/
theorem noS8R130_Law4409 : ∀ v : Magma.tup8R130,
    ¬ @Equation4409 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4424 takes them (3 nodes). -/
def ordS8R130_Law4424 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4424. -/
theorem noS8R130_Law4424 : ∀ v : Magma.tup8R130,
    ¬ @Equation4424 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4424) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4424) (by native_decide) v.1 v.2
    ((@Law4424.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (3 nodes). -/
def ordS8R130_Law4433 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4433. -/
theorem noS8R130_Law4433 : ∀ v : Magma.tup8R130,
    ¬ @Equation4433 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4436 takes them (3 nodes). -/
def ordS8R130_Law4436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4436. -/
theorem noS8R130_Law4436 : ∀ v : Magma.tup8R130,
    ¬ @Equation4436 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4436) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4436) (by native_decide) v.1 v.2
    ((@Law4436.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4442 takes them (3 nodes). -/
def ordS8R130_Law4442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4442. -/
theorem noS8R130_Law4442 : ∀ v : Magma.tup8R130,
    ¬ @Equation4442 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4442) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4442) (by native_decide) v.1 v.2
    ((@Law4442.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4445 takes them (3 nodes). -/
def ordS8R130_Law4445 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4445. -/
theorem noS8R130_Law4445 : ∀ v : Magma.tup8R130,
    ¬ @Equation4445 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4445) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4445) (by native_decide) v.1 v.2
    ((@Law4445.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4469 takes them (3 nodes). -/
def ordS8R130_Law4469 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4469. -/
theorem noS8R130_Law4469 : ∀ v : Magma.tup8R130,
    ¬ @Equation4469 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4469) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4469) (by native_decide) v.1 v.2
    ((@Law4469.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4471 takes them (3 nodes). -/
def ordS8R130_Law4471 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4471. -/
theorem noS8R130_Law4471 : ∀ v : Magma.tup8R130,
    ¬ @Equation4471 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4471) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4471) (by native_decide) v.1 v.2
    ((@Law4471.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4472 takes them (3 nodes). -/
def ordS8R130_Law4472 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4472. -/
theorem noS8R130_Law4472 : ∀ v : Magma.tup8R130,
    ¬ @Equation4472 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4473 takes them (4 nodes). -/
def ordS8R130_Law4473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4473. -/
theorem noS8R130_Law4473 : ∀ v : Magma.tup8R130,
    ¬ @Equation4473 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4473) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4473) (by native_decide) v.1 v.2
    ((@Law4473.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4477 takes them (3 nodes). -/
def ordS8R130_Law4477 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4477. -/
theorem noS8R130_Law4477 : ∀ v : Magma.tup8R130,
    ¬ @Equation4477 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4477) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4477) (by native_decide) v.1 v.2
    ((@Law4477.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4480 takes them (3 nodes). -/
def ordS8R130_Law4480 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4480. -/
theorem noS8R130_Law4480 : ∀ v : Magma.tup8R130,
    ¬ @Equation4480 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4483 takes them (3 nodes). -/
def ordS8R130_Law4483 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4483. -/
theorem noS8R130_Law4483 : ∀ v : Magma.tup8R130,
    ¬ @Equation4483 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4483) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4483) (by native_decide) v.1 v.2
    ((@Law4483.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4498 takes them (3 nodes). -/
def ordS8R130_Law4498 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4498. -/
theorem noS8R130_Law4498 : ∀ v : Magma.tup8R130,
    ¬ @Equation4498 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4498) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4498) (by native_decide) v.1 v.2
    ((@Law4498.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4512 takes them (4 nodes). -/
def ordS8R130_Law4512 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4512. -/
theorem noS8R130_Law4512 : ∀ v : Magma.tup8R130,
    ¬ @Equation4512 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4512) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4512) (by native_decide) v.1 v.2
    ((@Law4512.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4515 takes them (3 nodes). -/
def ordS8R130_Law4515 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4515. -/
theorem noS8R130_Law4515 : ∀ v : Magma.tup8R130,
    ¬ @Equation4515 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4515) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4515) (by native_decide) v.1 v.2
    ((@Law4515.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4525 takes them (3 nodes). -/
def ordS8R130_Law4525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4525. -/
theorem noS8R130_Law4525 : ∀ v : Magma.tup8R130,
    ¬ @Equation4525 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4525) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4525) (by native_decide) v.1 v.2
    ((@Law4525.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4583 takes them (3 nodes). -/
def ordS8R130_Law4583 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4583. -/
theorem noS8R130_Law4583 : ∀ v : Magma.tup8R130,
    ¬ @Equation4583 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4583) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4583) (by native_decide) v.1 v.2
    ((@Law4583.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (3 nodes). -/
def ordS8R130_Law4585 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4585. -/
theorem noS8R130_Law4585 : ∀ v : Magma.tup8R130,
    ¬ @Equation4585 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4587 takes them (3 nodes). -/
def ordS8R130_Law4587 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4587. -/
theorem noS8R130_Law4587 : ∀ v : Magma.tup8R130,
    ¬ @Equation4587 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4587) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4587) (by native_decide) v.1 v.2
    ((@Law4587.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4590 takes them (3 nodes). -/
def ordS8R130_Law4590 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4590. -/
theorem noS8R130_Law4590 : ∀ v : Magma.tup8R130,
    ¬ @Equation4590 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4590) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4590) (by native_decide) v.1 v.2
    ((@Law4590.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4597 takes them (3 nodes). -/
def ordS8R130_Law4597 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4597. -/
theorem noS8R130_Law4597 : ∀ v : Magma.tup8R130,
    ¬ @Equation4597 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4597) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4597) (by native_decide) v.1 v.2
    ((@Law4597.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4598 takes them (3 nodes). -/
def ordS8R130_Law4598 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4598. -/
theorem noS8R130_Law4598 : ∀ v : Magma.tup8R130,
    ¬ @Equation4598 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4598) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4598) (by native_decide) v.1 v.2
    ((@Law4598.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4599 takes them (4 nodes). -/
def ordS8R130_Law4599 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4599. -/
theorem noS8R130_Law4599 : ∀ v : Magma.tup8R130,
    ¬ @Equation4599 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4599) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4599) (by native_decide) v.1 v.2
    ((@Law4599.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4606 takes them (3 nodes). -/
def ordS8R130_Law4606 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4606. -/
theorem noS8R130_Law4606 : ∀ v : Magma.tup8R130,
    ¬ @Equation4606 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4606) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4606) (by native_decide) v.1 v.2
    ((@Law4606.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4622 takes them (3 nodes). -/
def ordS8R130_Law4622 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4622. -/
theorem noS8R130_Law4622 : ∀ v : Magma.tup8R130,
    ¬ @Equation4622 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4622) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4622) (by native_decide) v.1 v.2
    ((@Law4622.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (3 nodes). -/
def ordS8R130_Law4629 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4629. -/
theorem noS8R130_Law4629 : ∀ v : Magma.tup8R130,
    ¬ @Equation4629 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (3 nodes). -/
def ordS8R130_Law4635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4635. -/
theorem noS8R130_Law4635 : ∀ v : Magma.tup8R130,
    ¬ @Equation4635 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (3 nodes). -/
def ordS8R130_Law4656 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4656. -/
theorem noS8R130_Law4656 : ∀ v : Magma.tup8R130,
    ¬ @Equation4656 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4666 takes them (3 nodes). -/
def ordS8R130_Law4666 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4666. -/
theorem noS8R130_Law4666 : ∀ v : Magma.tup8R130,
    ¬ @Equation4666 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4666) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4666) (by native_decide) v.1 v.2
    ((@Law4666.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (3 nodes). -/
def ordS8R130_Law4673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4673. -/
theorem noS8R130_Law4673 : ∀ v : Magma.tup8R130,
    ¬ @Equation4673 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (3 nodes). -/
def ordS8R130_Law4677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4677. -/
theorem noS8R130_Law4677 : ∀ v : Magma.tup8R130,
    ¬ @Equation4677 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `72` equations. -/
theorem srch8R130_refutes_6 :
    FamilyRefutes Magma.srch8R130 [
      4096, 4100, 4120, 4121, 4127, 4128, 4130, 4131, 4135, 4143, 4146, 4155, 4158, 4165, 4192,
      4200, 4226, 4268, 4270, 4272, 4275, 4282, 4283, 4284, 4291, 4307, 4314, 4320, 4341, 4351,
      4358, 4362, 4381, 4383, 4385, 4388, 4395, 4396, 4398, 4406, 4409, 4424, 4433, 4436, 4442,
      4445, 4469, 4471, 4472, 4473, 4477, 4480, 4483, 4498, 4512, 4515, 4525, 4583, 4585, 4587,
      4590, 4597, 4598, 4599, 4606, 4622, 4629, 4635, 4656, 4666, 4673, 4677
    ] :=
  ⟨noS8R130_Law4096, noS8R130_Law4100, noS8R130_Law4120, noS8R130_Law4121, noS8R130_Law4127, noS8R130_Law4128, noS8R130_Law4130, noS8R130_Law4131, noS8R130_Law4135, noS8R130_Law4143, noS8R130_Law4146, noS8R130_Law4155, noS8R130_Law4158, noS8R130_Law4165, noS8R130_Law4192, noS8R130_Law4200, noS8R130_Law4226, noS8R130_Law4268, noS8R130_Law4270, noS8R130_Law4272, noS8R130_Law4275, noS8R130_Law4282, noS8R130_Law4283, noS8R130_Law4284, noS8R130_Law4291, noS8R130_Law4307, noS8R130_Law4314, noS8R130_Law4320, noS8R130_Law4341, noS8R130_Law4351, noS8R130_Law4358, noS8R130_Law4362, noS8R130_Law4381, noS8R130_Law4383, noS8R130_Law4385, noS8R130_Law4388, noS8R130_Law4395, noS8R130_Law4396, noS8R130_Law4398, noS8R130_Law4406, noS8R130_Law4409, noS8R130_Law4424, noS8R130_Law4433, noS8R130_Law4436, noS8R130_Law4442, noS8R130_Law4445, noS8R130_Law4469, noS8R130_Law4471, noS8R130_Law4472, noS8R130_Law4473, noS8R130_Law4477, noS8R130_Law4480, noS8R130_Law4483, noS8R130_Law4498, noS8R130_Law4512, noS8R130_Law4515, noS8R130_Law4525, noS8R130_Law4583, noS8R130_Law4585, noS8R130_Law4587, noS8R130_Law4590, noS8R130_Law4597, noS8R130_Law4598, noS8R130_Law4599, noS8R130_Law4606, noS8R130_Law4622, noS8R130_Law4629, noS8R130_Law4635, noS8R130_Law4656, noS8R130_Law4666, noS8R130_Law4673, noS8R130_Law4677⟩

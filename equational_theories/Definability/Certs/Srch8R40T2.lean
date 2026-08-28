import equational_theories.Definability.Srch_S8R40

/-!
# Structural certificate targets: `Magma.srch8R40` (part 3 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R40_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `28` equations here, 2,612 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R40_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4072 takes them (249 nodes). -/
def ordS8R40_Law4072 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4072. -/
theorem noS8R40_Law4072 : ∀ v : Magma.tup8R40,
    ¬ @Equation4072 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4072) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4072) (by native_decide) v.1 v.2
    ((@Law4072.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4075 takes them (74 nodes). -/
def ordS8R40_Law4075 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4075. -/
theorem noS8R40_Law4075 : ∀ v : Magma.tup8R40,
    ¬ @Equation4075 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4075) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4075) (by native_decide) v.1 v.2
    ((@Law4075.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4077 takes them (135 nodes). -/
def ordS8R40_Law4077 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4077. -/
theorem noS8R40_Law4077 : ∀ v : Magma.tup8R40,
    ¬ @Equation4077 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4077) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4077) (by native_decide) v.1 v.2
    ((@Law4077.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4078 takes them (113 nodes). -/
def ordS8R40_Law4078 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4078. -/
theorem noS8R40_Law4078 : ∀ v : Magma.tup8R40,
    ¬ @Equation4078 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4078) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4078) (by native_decide) v.1 v.2
    ((@Law4078.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4079 takes them (43 nodes). -/
def ordS8R40_Law4079 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4079. -/
theorem noS8R40_Law4079 : ∀ v : Magma.tup8R40,
    ¬ @Equation4079 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4079) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4079) (by native_decide) v.1 v.2
    ((@Law4079.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4278 takes them (59 nodes). -/
def ordS8R40_Law4278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4278. -/
theorem noS8R40_Law4278 : ∀ v : Magma.tup8R40,
    ¬ @Equation4278 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4278) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4278) (by native_decide) v.1 v.2
    ((@Law4278.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4296 takes them (62 nodes). -/
def ordS8R40_Law4296 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4296. -/
theorem noS8R40_Law4296 : ∀ v : Magma.tup8R40,
    ¬ @Equation4296 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4296) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4296) (by native_decide) v.1 v.2
    ((@Law4296.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4304 takes them (70 nodes). -/
def ordS8R40_Law4304 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4304. -/
theorem noS8R40_Law4304 : ∀ v : Magma.tup8R40,
    ¬ @Equation4304 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4304) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4304) (by native_decide) v.1 v.2
    ((@Law4304.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4310 takes them (31 nodes). -/
def ordS8R40_Law4310 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4310. -/
theorem noS8R40_Law4310 : ∀ v : Magma.tup8R40,
    ¬ @Equation4310 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4323 takes them (67 nodes). -/
def ordS8R40_Law4323 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4323. -/
theorem noS8R40_Law4323 : ∀ v : Magma.tup8R40,
    ¬ @Equation4323 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4327 takes them (121 nodes). -/
def ordS8R40_Law4327 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4327. -/
theorem noS8R40_Law4327 : ∀ v : Magma.tup8R40,
    ¬ @Equation4327 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4327) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4327) (by native_decide) v.1 v.2
    ((@Law4327.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4334 takes them (51 nodes). -/
def ordS8R40_Law4334 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4334. -/
theorem noS8R40_Law4334 : ∀ v : Magma.tup8R40,
    ¬ @Equation4334 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4334) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4334) (by native_decide) v.1 v.2
    ((@Law4334.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4348 takes them (82 nodes). -/
def ordS8R40_Law4348 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4348. -/
theorem noS8R40_Law4348 : ∀ v : Magma.tup8R40,
    ¬ @Equation4348 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (59 nodes). -/
def ordS8R40_Law4354 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4354. -/
theorem noS8R40_Law4354 : ∀ v : Magma.tup8R40,
    ¬ @Equation4354 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4367 takes them (32 nodes). -/
def ordS8R40_Law4367 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4367. -/
theorem noS8R40_Law4367 : ∀ v : Magma.tup8R40,
    ¬ @Equation4367 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4378 takes them (31 nodes). -/
def ordS8R40_Law4378 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4378. -/
theorem noS8R40_Law4378 : ∀ v : Magma.tup8R40,
    ¬ @Equation4378 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4378) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 5)
    (ord := ordS8R40_Law4378) (by native_decide) v.1 v.2
    ((@Law4378.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4384 takes them (39 nodes). -/
def ordS8R40_Law4384 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4384. -/
theorem noS8R40_Law4384 : ∀ v : Magma.tup8R40,
    ¬ @Equation4384 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4384) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4384) (by native_decide) v.1 v.2
    ((@Law4384.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (157 nodes). -/
def ordS8R40_Law4401 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4401. -/
theorem noS8R40_Law4401 : ∀ v : Magma.tup8R40,
    ¬ @Equation4401 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4402 takes them (105 nodes). -/
def ordS8R40_Law4402 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4402. -/
theorem noS8R40_Law4402 : ∀ v : Magma.tup8R40,
    ¬ @Equation4402 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4402) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4402) (by native_decide) v.1 v.2
    ((@Law4402.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4403 takes them (80 nodes). -/
def ordS8R40_Law4403 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4403. -/
theorem noS8R40_Law4403 : ∀ v : Magma.tup8R40,
    ¬ @Equation4403 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4403) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4403) (by native_decide) v.1 v.2
    ((@Law4403.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4412 takes them (74 nodes). -/
def ordS8R40_Law4412 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4412. -/
theorem noS8R40_Law4412 : ∀ v : Magma.tup8R40,
    ¬ @Equation4412 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4412) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4412) (by native_decide) v.1 v.2
    ((@Law4412.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4416 takes them (179 nodes). -/
def ordS8R40_Law4416 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4416. -/
theorem noS8R40_Law4416 : ∀ v : Magma.tup8R40,
    ¬ @Equation4416 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4416) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4416) (by native_decide) v.1 v.2
    ((@Law4416.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4420 takes them (67 nodes). -/
def ordS8R40_Law4420 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4420. -/
theorem noS8R40_Law4420 : ∀ v : Magma.tup8R40,
    ¬ @Equation4420 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4420) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4420) (by native_decide) v.1 v.2
    ((@Law4420.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4438 takes them (272 nodes). -/
def ordS8R40_Law4438 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4438. -/
theorem noS8R40_Law4438 : ∀ v : Magma.tup8R40,
    ¬ @Equation4438 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4438) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4438) (by native_decide) v.1 v.2
    ((@Law4438.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4439 takes them (87 nodes). -/
def ordS8R40_Law4439 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4439. -/
theorem noS8R40_Law4439 : ∀ v : Magma.tup8R40,
    ¬ @Equation4439 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4439) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4439) (by native_decide) v.1 v.2
    ((@Law4439.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4440 takes them (128 nodes). -/
def ordS8R40_Law4440 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4440. -/
theorem noS8R40_Law4440 : ∀ v : Magma.tup8R40,
    ¬ @Equation4440 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4440) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4440) (by native_decide) v.1 v.2
    ((@Law4440.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4441 takes them (39 nodes). -/
def ordS8R40_Law4441 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4441. -/
theorem noS8R40_Law4441 : ∀ v : Magma.tup8R40,
    ¬ @Equation4441 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4441) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4441) (by native_decide) v.1 v.2
    ((@Law4441.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4448 takes them (106 nodes). -/
def ordS8R40_Law4448 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4448. -/
theorem noS8R40_Law4448 : ∀ v : Magma.tup8R40,
    ¬ @Equation4448 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4448) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4448) (by native_decide) v.1 v.2
    ((@Law4448.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- No member of the class satisfies any of these `28` equations. -/
theorem srch8R40_refutes_2 :
    FamilyRefutes Magma.srch8R40 [
      4072, 4075, 4077, 4078, 4079, 4278, 4296, 4304, 4310, 4323, 4327, 4334, 4348, 4354, 4367,
      4378, 4384, 4401, 4402, 4403, 4412, 4416, 4420, 4438, 4439, 4440, 4441, 4448
    ] :=
  ⟨noS8R40_Law4072, noS8R40_Law4075, noS8R40_Law4077, noS8R40_Law4078, noS8R40_Law4079, noS8R40_Law4278, noS8R40_Law4296, noS8R40_Law4304, noS8R40_Law4310, noS8R40_Law4323, noS8R40_Law4327, noS8R40_Law4334, noS8R40_Law4348, noS8R40_Law4354, noS8R40_Law4367, noS8R40_Law4378, noS8R40_Law4384, noS8R40_Law4401, noS8R40_Law4402, noS8R40_Law4403, noS8R40_Law4412, noS8R40_Law4416, noS8R40_Law4420, noS8R40_Law4438, noS8R40_Law4439, noS8R40_Law4440, noS8R40_Law4441, noS8R40_Law4448⟩

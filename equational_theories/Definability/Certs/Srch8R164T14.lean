import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 15 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `81` equations here, 737 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4366 takes them (6 nodes). -/
def ordS8R164_Law4366 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4366. -/
theorem noS8R164_Law4366 : ∀ v : Magma.tup8R164,
    ¬ @Equation4366 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4366) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4366) (by native_decide) v.1 v.2
    ((@Law4366.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4367 takes them (10 nodes). -/
def ordS8R164_Law4367 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4367. -/
theorem noS8R164_Law4367 : ∀ v : Magma.tup8R164,
    ¬ @Equation4367 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4368 takes them (6 nodes). -/
def ordS8R164_Law4368 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4368. -/
theorem noS8R164_Law4368 : ∀ v : Magma.tup8R164,
    ¬ @Equation4368 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4368) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4368) (by native_decide) v.1 v.2
    ((@Law4368.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4370 takes them (6 nodes). -/
def ordS8R164_Law4370 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4370. -/
theorem noS8R164_Law4370 : ∀ v : Magma.tup8R164,
    ¬ @Equation4370 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4370) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4370) (by native_decide) v.1 v.2
    ((@Law4370.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4371 takes them (7 nodes). -/
def ordS8R164_Law4371 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4371. -/
theorem noS8R164_Law4371 : ∀ v : Magma.tup8R164,
    ¬ @Equation4371 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4371) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4371) (by native_decide) v.1 v.2
    ((@Law4371.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4372 takes them (7 nodes). -/
def ordS8R164_Law4372 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4372. -/
theorem noS8R164_Law4372 : ∀ v : Magma.tup8R164,
    ¬ @Equation4372 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4372) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4372) (by native_decide) v.1 v.2
    ((@Law4372.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4373 takes them (6 nodes). -/
def ordS8R164_Law4373 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4373. -/
theorem noS8R164_Law4373 : ∀ v : Magma.tup8R164,
    ¬ @Equation4373 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4373) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4373) (by native_decide) v.1 v.2
    ((@Law4373.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4374 takes them (10 nodes). -/
def ordS8R164_Law4374 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4374. -/
theorem noS8R164_Law4374 : ∀ v : Magma.tup8R164,
    ¬ @Equation4374 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4374) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4374) (by native_decide) v.1 v.2
    ((@Law4374.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4375 takes them (6 nodes). -/
def ordS8R164_Law4375 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4375. -/
theorem noS8R164_Law4375 : ∀ v : Magma.tup8R164,
    ¬ @Equation4375 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4375) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4375) (by native_decide) v.1 v.2
    ((@Law4375.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4376 takes them (7 nodes). -/
def ordS8R164_Law4376 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4376. -/
theorem noS8R164_Law4376 : ∀ v : Magma.tup8R164,
    ¬ @Equation4376 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4376) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4376) (by native_decide) v.1 v.2
    ((@Law4376.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4377 takes them (6 nodes). -/
def ordS8R164_Law4377 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4377. -/
theorem noS8R164_Law4377 : ∀ v : Magma.tup8R164,
    ¬ @Equation4377 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4377) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4377) (by native_decide) v.1 v.2
    ((@Law4377.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4378 takes them (10 nodes). -/
def ordS8R164_Law4378 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4378. -/
theorem noS8R164_Law4378 : ∀ v : Magma.tup8R164,
    ¬ @Equation4378 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4378) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4378) (by native_decide) v.1 v.2
    ((@Law4378.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4379 takes them (6 nodes). -/
def ordS8R164_Law4379 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4379. -/
theorem noS8R164_Law4379 : ∀ v : Magma.tup8R164,
    ¬ @Equation4379 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4379) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law4379) (by native_decide) v.1 v.2
    ((@Law4379.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4382 takes them (17 nodes). -/
def ordS8R164_Law4382 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4382. -/
theorem noS8R164_Law4382 : ∀ v : Magma.tup8R164,
    ¬ @Equation4382 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4382) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4382) (by native_decide) v.1 v.2
    ((@Law4382.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4384 takes them (9 nodes). -/
def ordS8R164_Law4384 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4384. -/
theorem noS8R164_Law4384 : ∀ v : Magma.tup8R164,
    ¬ @Equation4384 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4384) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4384) (by native_decide) v.1 v.2
    ((@Law4384.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4385 takes them (12 nodes). -/
def ordS8R164_Law4385 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4385. -/
theorem noS8R164_Law4385 : ∀ v : Magma.tup8R164,
    ¬ @Equation4385 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4385) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4385) (by native_decide) v.1 v.2
    ((@Law4385.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4387 takes them (6 nodes). -/
def ordS8R164_Law4387 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4387. -/
theorem noS8R164_Law4387 : ∀ v : Magma.tup8R164,
    ¬ @Equation4387 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4387) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4387) (by native_decide) v.1 v.2
    ((@Law4387.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4391 takes them (10 nodes). -/
def ordS8R164_Law4391 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4391. -/
theorem noS8R164_Law4391 : ∀ v : Magma.tup8R164,
    ¬ @Equation4391 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4391) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4391) (by native_decide) v.1 v.2
    ((@Law4391.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4392 takes them (9 nodes). -/
def ordS8R164_Law4392 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4392. -/
theorem noS8R164_Law4392 : ∀ v : Magma.tup8R164,
    ¬ @Equation4392 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4392) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4392) (by native_decide) v.1 v.2
    ((@Law4392.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4393 takes them (9 nodes). -/
def ordS8R164_Law4393 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4393. -/
theorem noS8R164_Law4393 : ∀ v : Magma.tup8R164,
    ¬ @Equation4393 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4393) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4393) (by native_decide) v.1 v.2
    ((@Law4393.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4394 takes them (6 nodes). -/
def ordS8R164_Law4394 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4394. -/
theorem noS8R164_Law4394 : ∀ v : Magma.tup8R164,
    ¬ @Equation4394 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4394) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4394) (by native_decide) v.1 v.2
    ((@Law4394.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4395 takes them (11 nodes). -/
def ordS8R164_Law4395 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4395. -/
theorem noS8R164_Law4395 : ∀ v : Magma.tup8R164,
    ¬ @Equation4395 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4395) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4395) (by native_decide) v.1 v.2
    ((@Law4395.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4397 takes them (10 nodes). -/
def ordS8R164_Law4397 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4397. -/
theorem noS8R164_Law4397 : ∀ v : Magma.tup8R164,
    ¬ @Equation4397 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4397) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4397) (by native_decide) v.1 v.2
    ((@Law4397.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4399 takes them (23 nodes). -/
def ordS8R164_Law4399 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4399. -/
theorem noS8R164_Law4399 : ∀ v : Magma.tup8R164,
    ¬ @Equation4399 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4399) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4399) (by native_decide) v.1 v.2
    ((@Law4399.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4400 takes them (9 nodes). -/
def ordS8R164_Law4400 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4400. -/
theorem noS8R164_Law4400 : ∀ v : Magma.tup8R164,
    ¬ @Equation4400 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4400) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4400) (by native_decide) v.1 v.2
    ((@Law4400.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (10 nodes). -/
def ordS8R164_Law4401 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4401. -/
theorem noS8R164_Law4401 : ∀ v : Magma.tup8R164,
    ¬ @Equation4401 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4402 takes them (13 nodes). -/
def ordS8R164_Law4402 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4402. -/
theorem noS8R164_Law4402 : ∀ v : Magma.tup8R164,
    ¬ @Equation4402 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4402) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4402) (by native_decide) v.1 v.2
    ((@Law4402.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4403 takes them (9 nodes). -/
def ordS8R164_Law4403 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4403. -/
theorem noS8R164_Law4403 : ∀ v : Magma.tup8R164,
    ¬ @Equation4403 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4403) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4403) (by native_decide) v.1 v.2
    ((@Law4403.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4404 takes them (9 nodes). -/
def ordS8R164_Law4404 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4404. -/
theorem noS8R164_Law4404 : ∀ v : Magma.tup8R164,
    ¬ @Equation4404 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4404) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4404) (by native_decide) v.1 v.2
    ((@Law4404.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4406 takes them (19 nodes). -/
def ordS8R164_Law4406 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4406. -/
theorem noS8R164_Law4406 : ∀ v : Magma.tup8R164,
    ¬ @Equation4406 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4407 takes them (6 nodes). -/
def ordS8R164_Law4407 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4407. -/
theorem noS8R164_Law4407 : ∀ v : Magma.tup8R164,
    ¬ @Equation4407 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4407) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4407) (by native_decide) v.1 v.2
    ((@Law4407.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4408 takes them (13 nodes). -/
def ordS8R164_Law4408 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4408. -/
theorem noS8R164_Law4408 : ∀ v : Magma.tup8R164,
    ¬ @Equation4408 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4408) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4408) (by native_decide) v.1 v.2
    ((@Law4408.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4410 takes them (8 nodes). -/
def ordS8R164_Law4410 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4410. -/
theorem noS8R164_Law4410 : ∀ v : Magma.tup8R164,
    ¬ @Equation4410 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4410) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4410) (by native_decide) v.1 v.2
    ((@Law4410.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4411 takes them (7 nodes). -/
def ordS8R164_Law4411 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4411. -/
theorem noS8R164_Law4411 : ∀ v : Magma.tup8R164,
    ¬ @Equation4411 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4411) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4411) (by native_decide) v.1 v.2
    ((@Law4411.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4412 takes them (12 nodes). -/
def ordS8R164_Law4412 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4412. -/
theorem noS8R164_Law4412 : ∀ v : Magma.tup8R164,
    ¬ @Equation4412 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4412) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4412) (by native_decide) v.1 v.2
    ((@Law4412.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4414 takes them (6 nodes). -/
def ordS8R164_Law4414 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4414. -/
theorem noS8R164_Law4414 : ∀ v : Magma.tup8R164,
    ¬ @Equation4414 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4414) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4414) (by native_decide) v.1 v.2
    ((@Law4414.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4415 takes them (6 nodes). -/
def ordS8R164_Law4415 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4415. -/
theorem noS8R164_Law4415 : ∀ v : Magma.tup8R164,
    ¬ @Equation4415 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4415) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4415) (by native_decide) v.1 v.2
    ((@Law4415.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4416 takes them (10 nodes). -/
def ordS8R164_Law4416 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4416. -/
theorem noS8R164_Law4416 : ∀ v : Magma.tup8R164,
    ¬ @Equation4416 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4416) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4416) (by native_decide) v.1 v.2
    ((@Law4416.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4417 takes them (8 nodes). -/
def ordS8R164_Law4417 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4417. -/
theorem noS8R164_Law4417 : ∀ v : Magma.tup8R164,
    ¬ @Equation4417 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4417) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4417) (by native_decide) v.1 v.2
    ((@Law4417.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4418 takes them (6 nodes). -/
def ordS8R164_Law4418 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4418. -/
theorem noS8R164_Law4418 : ∀ v : Magma.tup8R164,
    ¬ @Equation4418 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4418) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4418) (by native_decide) v.1 v.2
    ((@Law4418.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4419 takes them (7 nodes). -/
def ordS8R164_Law4419 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4419. -/
theorem noS8R164_Law4419 : ∀ v : Magma.tup8R164,
    ¬ @Equation4419 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4419) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4419) (by native_decide) v.1 v.2
    ((@Law4419.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4420 takes them (10 nodes). -/
def ordS8R164_Law4420 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4420. -/
theorem noS8R164_Law4420 : ∀ v : Magma.tup8R164,
    ¬ @Equation4420 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4420) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4420) (by native_decide) v.1 v.2
    ((@Law4420.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4422 takes them (6 nodes). -/
def ordS8R164_Law4422 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4422. -/
theorem noS8R164_Law4422 : ∀ v : Magma.tup8R164,
    ¬ @Equation4422 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4422) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4422) (by native_decide) v.1 v.2
    ((@Law4422.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4423 takes them (8 nodes). -/
def ordS8R164_Law4423 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4423. -/
theorem noS8R164_Law4423 : ∀ v : Magma.tup8R164,
    ¬ @Equation4423 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4423) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4423) (by native_decide) v.1 v.2
    ((@Law4423.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4425 takes them (8 nodes). -/
def ordS8R164_Law4425 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4425. -/
theorem noS8R164_Law4425 : ∀ v : Magma.tup8R164,
    ¬ @Equation4425 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4425) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4425) (by native_decide) v.1 v.2
    ((@Law4425.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4426 takes them (8 nodes). -/
def ordS8R164_Law4426 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4426. -/
theorem noS8R164_Law4426 : ∀ v : Magma.tup8R164,
    ¬ @Equation4426 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4426) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4426) (by native_decide) v.1 v.2
    ((@Law4426.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4427 takes them (6 nodes). -/
def ordS8R164_Law4427 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4427. -/
theorem noS8R164_Law4427 : ∀ v : Magma.tup8R164,
    ¬ @Equation4427 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4427) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4427) (by native_decide) v.1 v.2
    ((@Law4427.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4428 takes them (10 nodes). -/
def ordS8R164_Law4428 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4428. -/
theorem noS8R164_Law4428 : ∀ v : Magma.tup8R164,
    ¬ @Equation4428 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4428) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4428) (by native_decide) v.1 v.2
    ((@Law4428.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4429 takes them (8 nodes). -/
def ordS8R164_Law4429 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4429. -/
theorem noS8R164_Law4429 : ∀ v : Magma.tup8R164,
    ¬ @Equation4429 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4429) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4429) (by native_decide) v.1 v.2
    ((@Law4429.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4430 takes them (6 nodes). -/
def ordS8R164_Law4430 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4430. -/
theorem noS8R164_Law4430 : ∀ v : Magma.tup8R164,
    ¬ @Equation4430 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4430) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4430) (by native_decide) v.1 v.2
    ((@Law4430.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4431 takes them (6 nodes). -/
def ordS8R164_Law4431 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4431. -/
theorem noS8R164_Law4431 : ∀ v : Magma.tup8R164,
    ¬ @Equation4431 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4431) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4431) (by native_decide) v.1 v.2
    ((@Law4431.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4432 takes them (17 nodes). -/
def ordS8R164_Law4432 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4432. -/
theorem noS8R164_Law4432 : ∀ v : Magma.tup8R164,
    ¬ @Equation4432 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4432) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4432) (by native_decide) v.1 v.2
    ((@Law4432.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4434 takes them (10 nodes). -/
def ordS8R164_Law4434 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4434. -/
theorem noS8R164_Law4434 : ∀ v : Magma.tup8R164,
    ¬ @Equation4434 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4434) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4434) (by native_decide) v.1 v.2
    ((@Law4434.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4436 takes them (19 nodes). -/
def ordS8R164_Law4436 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4436. -/
theorem noS8R164_Law4436 : ∀ v : Magma.tup8R164,
    ¬ @Equation4436 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4436) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4436) (by native_decide) v.1 v.2
    ((@Law4436.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4437 takes them (9 nodes). -/
def ordS8R164_Law4437 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4437. -/
theorem noS8R164_Law4437 : ∀ v : Magma.tup8R164,
    ¬ @Equation4437 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4437) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4437) (by native_decide) v.1 v.2
    ((@Law4437.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4438 takes them (15 nodes). -/
def ordS8R164_Law4438 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4438. -/
theorem noS8R164_Law4438 : ∀ v : Magma.tup8R164,
    ¬ @Equation4438 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4438) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4438) (by native_decide) v.1 v.2
    ((@Law4438.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4439 takes them (10 nodes). -/
def ordS8R164_Law4439 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4439. -/
theorem noS8R164_Law4439 : ∀ v : Magma.tup8R164,
    ¬ @Equation4439 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4439) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4439) (by native_decide) v.1 v.2
    ((@Law4439.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4440 takes them (12 nodes). -/
def ordS8R164_Law4440 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4440. -/
theorem noS8R164_Law4440 : ∀ v : Magma.tup8R164,
    ¬ @Equation4440 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4440) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4440) (by native_decide) v.1 v.2
    ((@Law4440.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4441 takes them (9 nodes). -/
def ordS8R164_Law4441 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4441. -/
theorem noS8R164_Law4441 : ∀ v : Magma.tup8R164,
    ¬ @Equation4441 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4441) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4441) (by native_decide) v.1 v.2
    ((@Law4441.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4443 takes them (11 nodes). -/
def ordS8R164_Law4443 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4443. -/
theorem noS8R164_Law4443 : ∀ v : Magma.tup8R164,
    ¬ @Equation4443 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4443) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4443) (by native_decide) v.1 v.2
    ((@Law4443.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4444 takes them (6 nodes). -/
def ordS8R164_Law4444 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4444. -/
theorem noS8R164_Law4444 : ∀ v : Magma.tup8R164,
    ¬ @Equation4444 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4444) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4444) (by native_decide) v.1 v.2
    ((@Law4444.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4445 takes them (18 nodes). -/
def ordS8R164_Law4445 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4445. -/
theorem noS8R164_Law4445 : ∀ v : Magma.tup8R164,
    ¬ @Equation4445 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4445) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4445) (by native_decide) v.1 v.2
    ((@Law4445.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4447 takes them (7 nodes). -/
def ordS8R164_Law4447 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4447. -/
theorem noS8R164_Law4447 : ∀ v : Magma.tup8R164,
    ¬ @Equation4447 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4447) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4447) (by native_decide) v.1 v.2
    ((@Law4447.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4448 takes them (10 nodes). -/
def ordS8R164_Law4448 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4448. -/
theorem noS8R164_Law4448 : ∀ v : Magma.tup8R164,
    ¬ @Equation4448 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4448) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4448) (by native_decide) v.1 v.2
    ((@Law4448.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4449 takes them (7 nodes). -/
def ordS8R164_Law4449 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4449. -/
theorem noS8R164_Law4449 : ∀ v : Magma.tup8R164,
    ¬ @Equation4449 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4449) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4449) (by native_decide) v.1 v.2
    ((@Law4449.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4451 takes them (6 nodes). -/
def ordS8R164_Law4451 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4451. -/
theorem noS8R164_Law4451 : ∀ v : Magma.tup8R164,
    ¬ @Equation4451 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4451) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4451) (by native_decide) v.1 v.2
    ((@Law4451.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4452 takes them (11 nodes). -/
def ordS8R164_Law4452 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4452. -/
theorem noS8R164_Law4452 : ∀ v : Magma.tup8R164,
    ¬ @Equation4452 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4453 takes them (7 nodes). -/
def ordS8R164_Law4453 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4453. -/
theorem noS8R164_Law4453 : ∀ v : Magma.tup8R164,
    ¬ @Equation4453 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4453) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4453) (by native_decide) v.1 v.2
    ((@Law4453.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4454 takes them (7 nodes). -/
def ordS8R164_Law4454 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4454. -/
theorem noS8R164_Law4454 : ∀ v : Magma.tup8R164,
    ¬ @Equation4454 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4454) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4454) (by native_decide) v.1 v.2
    ((@Law4454.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4455 takes them (6 nodes). -/
def ordS8R164_Law4455 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4455. -/
theorem noS8R164_Law4455 : ∀ v : Magma.tup8R164,
    ¬ @Equation4455 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4455) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4455) (by native_decide) v.1 v.2
    ((@Law4455.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4456 takes them (10 nodes). -/
def ordS8R164_Law4456 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4456. -/
theorem noS8R164_Law4456 : ∀ v : Magma.tup8R164,
    ¬ @Equation4456 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4456) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4456) (by native_decide) v.1 v.2
    ((@Law4456.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4457 takes them (9 nodes). -/
def ordS8R164_Law4457 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4457. -/
theorem noS8R164_Law4457 : ∀ v : Magma.tup8R164,
    ¬ @Equation4457 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4457) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4457) (by native_decide) v.1 v.2
    ((@Law4457.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4459 takes them (6 nodes). -/
def ordS8R164_Law4459 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4459. -/
theorem noS8R164_Law4459 : ∀ v : Magma.tup8R164,
    ¬ @Equation4459 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4459) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4459) (by native_decide) v.1 v.2
    ((@Law4459.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4460 takes them (11 nodes). -/
def ordS8R164_Law4460 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4460. -/
theorem noS8R164_Law4460 : ∀ v : Magma.tup8R164,
    ¬ @Equation4460 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4460) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4460) (by native_decide) v.1 v.2
    ((@Law4460.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4462 takes them (9 nodes). -/
def ordS8R164_Law4462 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4462. -/
theorem noS8R164_Law4462 : ∀ v : Magma.tup8R164,
    ¬ @Equation4462 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4462) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4462) (by native_decide) v.1 v.2
    ((@Law4462.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4463 takes them (7 nodes). -/
def ordS8R164_Law4463 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4463. -/
theorem noS8R164_Law4463 : ∀ v : Magma.tup8R164,
    ¬ @Equation4463 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4463) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4463) (by native_decide) v.1 v.2
    ((@Law4463.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4464 takes them (10 nodes). -/
def ordS8R164_Law4464 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4464. -/
theorem noS8R164_Law4464 : ∀ v : Magma.tup8R164,
    ¬ @Equation4464 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4464) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4464) (by native_decide) v.1 v.2
    ((@Law4464.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4465 takes them (7 nodes). -/
def ordS8R164_Law4465 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4465. -/
theorem noS8R164_Law4465 : ∀ v : Magma.tup8R164,
    ¬ @Equation4465 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4465) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4465) (by native_decide) v.1 v.2
    ((@Law4465.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4466 takes them (7 nodes). -/
def ordS8R164_Law4466 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4466. -/
theorem noS8R164_Law4466 : ∀ v : Magma.tup8R164,
    ¬ @Equation4466 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4466) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4466) (by native_decide) v.1 v.2
    ((@Law4466.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4467 takes them (9 nodes). -/
def ordS8R164_Law4467 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4467. -/
theorem noS8R164_Law4467 : ∀ v : Magma.tup8R164,
    ¬ @Equation4467 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4467) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4467) (by native_decide) v.1 v.2
    ((@Law4467.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4468 takes them (6 nodes). -/
def ordS8R164_Law4468 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4468. -/
theorem noS8R164_Law4468 : ∀ v : Magma.tup8R164,
    ¬ @Equation4468 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4468) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4468) (by native_decide) v.1 v.2
    ((@Law4468.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `81` equations. -/
theorem srch8R164_refutes_14 :
    FamilyRefutes Magma.srch8R164 [
      4366, 4367, 4368, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378, 4379, 4382, 4384,
      4385, 4387, 4391, 4392, 4393, 4394, 4395, 4397, 4399, 4400, 4401, 4402, 4403, 4404, 4406,
      4407, 4408, 4410, 4411, 4412, 4414, 4415, 4416, 4417, 4418, 4419, 4420, 4422, 4423, 4425,
      4426, 4427, 4428, 4429, 4430, 4431, 4432, 4434, 4436, 4437, 4438, 4439, 4440, 4441, 4443,
      4444, 4445, 4447, 4448, 4449, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4459, 4460, 4462,
      4463, 4464, 4465, 4466, 4467, 4468
    ] :=
  ⟨noS8R164_Law4366, noS8R164_Law4367, noS8R164_Law4368, noS8R164_Law4370, noS8R164_Law4371, noS8R164_Law4372, noS8R164_Law4373, noS8R164_Law4374, noS8R164_Law4375, noS8R164_Law4376, noS8R164_Law4377, noS8R164_Law4378, noS8R164_Law4379, noS8R164_Law4382, noS8R164_Law4384, noS8R164_Law4385, noS8R164_Law4387, noS8R164_Law4391, noS8R164_Law4392, noS8R164_Law4393, noS8R164_Law4394, noS8R164_Law4395, noS8R164_Law4397, noS8R164_Law4399, noS8R164_Law4400, noS8R164_Law4401, noS8R164_Law4402, noS8R164_Law4403, noS8R164_Law4404, noS8R164_Law4406, noS8R164_Law4407, noS8R164_Law4408, noS8R164_Law4410, noS8R164_Law4411, noS8R164_Law4412, noS8R164_Law4414, noS8R164_Law4415, noS8R164_Law4416, noS8R164_Law4417, noS8R164_Law4418, noS8R164_Law4419, noS8R164_Law4420, noS8R164_Law4422, noS8R164_Law4423, noS8R164_Law4425, noS8R164_Law4426, noS8R164_Law4427, noS8R164_Law4428, noS8R164_Law4429, noS8R164_Law4430, noS8R164_Law4431, noS8R164_Law4432, noS8R164_Law4434, noS8R164_Law4436, noS8R164_Law4437, noS8R164_Law4438, noS8R164_Law4439, noS8R164_Law4440, noS8R164_Law4441, noS8R164_Law4443, noS8R164_Law4444, noS8R164_Law4445, noS8R164_Law4447, noS8R164_Law4448, noS8R164_Law4449, noS8R164_Law4451, noS8R164_Law4452, noS8R164_Law4453, noS8R164_Law4454, noS8R164_Law4455, noS8R164_Law4456, noS8R164_Law4457, noS8R164_Law4459, noS8R164_Law4460, noS8R164_Law4462, noS8R164_Law4463, noS8R164_Law4464, noS8R164_Law4465, noS8R164_Law4466, noS8R164_Law4467, noS8R164_Law4468⟩

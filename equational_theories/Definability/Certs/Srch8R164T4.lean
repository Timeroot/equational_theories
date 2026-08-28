import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 5 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `83` equations here, 635 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3335 takes them (9 nodes). -/
def ordS8R164_Law3335 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3335. -/
theorem noS8R164_Law3335 : ∀ v : Magma.tup8R164,
    ¬ @Equation3335 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3335) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3335) (by native_decide) v.1 v.2
    ((@Law3335.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3336 takes them (9 nodes). -/
def ordS8R164_Law3336 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3336. -/
theorem noS8R164_Law3336 : ∀ v : Magma.tup8R164,
    ¬ @Equation3336 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3336) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3336) (by native_decide) v.1 v.2
    ((@Law3336.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3337 takes them (9 nodes). -/
def ordS8R164_Law3337 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3337. -/
theorem noS8R164_Law3337 : ∀ v : Magma.tup8R164,
    ¬ @Equation3337 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3337) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3337) (by native_decide) v.1 v.2
    ((@Law3337.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3338 takes them (13 nodes). -/
def ordS8R164_Law3338 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3338. -/
theorem noS8R164_Law3338 : ∀ v : Magma.tup8R164,
    ¬ @Equation3338 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3338) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3338) (by native_decide) v.1 v.2
    ((@Law3338.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3339 takes them (9 nodes). -/
def ordS8R164_Law3339 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3339. -/
theorem noS8R164_Law3339 : ∀ v : Magma.tup8R164,
    ¬ @Equation3339 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3339) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3339) (by native_decide) v.1 v.2
    ((@Law3339.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3340 takes them (9 nodes). -/
def ordS8R164_Law3340 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3340. -/
theorem noS8R164_Law3340 : ∀ v : Magma.tup8R164,
    ¬ @Equation3340 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3340) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3340) (by native_decide) v.1 v.2
    ((@Law3340.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3341 takes them (9 nodes). -/
def ordS8R164_Law3341 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3341. -/
theorem noS8R164_Law3341 : ∀ v : Magma.tup8R164,
    ¬ @Equation3341 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3341) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3341) (by native_decide) v.1 v.2
    ((@Law3341.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (18 nodes). -/
def ordS8R164_Law3343 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3343. -/
theorem noS8R164_Law3343 : ∀ v : Magma.tup8R164,
    ¬ @Equation3343 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3344 takes them (6 nodes). -/
def ordS8R164_Law3344 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3344. -/
theorem noS8R164_Law3344 : ∀ v : Magma.tup8R164,
    ¬ @Equation3344 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3344) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3344) (by native_decide) v.1 v.2
    ((@Law3344.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3345 takes them (12 nodes). -/
def ordS8R164_Law3345 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3345. -/
theorem noS8R164_Law3345 : ∀ v : Magma.tup8R164,
    ¬ @Equation3345 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3345) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3345) (by native_decide) v.1 v.2
    ((@Law3345.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3347 takes them (6 nodes). -/
def ordS8R164_Law3347 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3347. -/
theorem noS8R164_Law3347 : ∀ v : Magma.tup8R164,
    ¬ @Equation3347 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3347) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3347) (by native_decide) v.1 v.2
    ((@Law3347.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3348 takes them (7 nodes). -/
def ordS8R164_Law3348 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3348. -/
theorem noS8R164_Law3348 : ∀ v : Magma.tup8R164,
    ¬ @Equation3348 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3348) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3348) (by native_decide) v.1 v.2
    ((@Law3348.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3349 takes them (10 nodes). -/
def ordS8R164_Law3349 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3349. -/
theorem noS8R164_Law3349 : ∀ v : Magma.tup8R164,
    ¬ @Equation3349 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3349) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3349) (by native_decide) v.1 v.2
    ((@Law3349.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3351 takes them (6 nodes). -/
def ordS8R164_Law3351 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3351. -/
theorem noS8R164_Law3351 : ∀ v : Magma.tup8R164,
    ¬ @Equation3351 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3351) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3351) (by native_decide) v.1 v.2
    ((@Law3351.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3352 takes them (12 nodes). -/
def ordS8R164_Law3352 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3352. -/
theorem noS8R164_Law3352 : ∀ v : Magma.tup8R164,
    ¬ @Equation3352 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3352) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3352) (by native_decide) v.1 v.2
    ((@Law3352.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3354 takes them (6 nodes). -/
def ordS8R164_Law3354 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3354. -/
theorem noS8R164_Law3354 : ∀ v : Magma.tup8R164,
    ¬ @Equation3354 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3354) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3354) (by native_decide) v.1 v.2
    ((@Law3354.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3356 takes them (10 nodes). -/
def ordS8R164_Law3356 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3356. -/
theorem noS8R164_Law3356 : ∀ v : Magma.tup8R164,
    ¬ @Equation3356 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3356) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3356) (by native_decide) v.1 v.2
    ((@Law3356.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3357 takes them (6 nodes). -/
def ordS8R164_Law3357 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3357. -/
theorem noS8R164_Law3357 : ∀ v : Magma.tup8R164,
    ¬ @Equation3357 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3357) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3357) (by native_decide) v.1 v.2
    ((@Law3357.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3358 takes them (7 nodes). -/
def ordS8R164_Law3358 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3358. -/
theorem noS8R164_Law3358 : ∀ v : Magma.tup8R164,
    ¬ @Equation3358 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3358) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3358) (by native_decide) v.1 v.2
    ((@Law3358.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3359 takes them (10 nodes). -/
def ordS8R164_Law3359 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3359. -/
theorem noS8R164_Law3359 : ∀ v : Magma.tup8R164,
    ¬ @Equation3359 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3359) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3359) (by native_decide) v.1 v.2
    ((@Law3359.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3360 takes them (7 nodes). -/
def ordS8R164_Law3360 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3360. -/
theorem noS8R164_Law3360 : ∀ v : Magma.tup8R164,
    ¬ @Equation3360 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3360) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3360) (by native_decide) v.1 v.2
    ((@Law3360.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3361 takes them (6 nodes). -/
def ordS8R164_Law3361 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3361. -/
theorem noS8R164_Law3361 : ∀ v : Magma.tup8R164,
    ¬ @Equation3361 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3361) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3361) (by native_decide) v.1 v.2
    ((@Law3361.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3362 takes them (7 nodes). -/
def ordS8R164_Law3362 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3362. -/
theorem noS8R164_Law3362 : ∀ v : Magma.tup8R164,
    ¬ @Equation3362 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3362) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3362) (by native_decide) v.1 v.2
    ((@Law3362.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3363 takes them (10 nodes). -/
def ordS8R164_Law3363 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3363. -/
theorem noS8R164_Law3363 : ∀ v : Magma.tup8R164,
    ¬ @Equation3363 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3363) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3363) (by native_decide) v.1 v.2
    ((@Law3363.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3365 takes them (6 nodes). -/
def ordS8R164_Law3365 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3365. -/
theorem noS8R164_Law3365 : ∀ v : Magma.tup8R164,
    ¬ @Equation3365 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3365) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3365) (by native_decide) v.1 v.2
    ((@Law3365.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3366 takes them (7 nodes). -/
def ordS8R164_Law3366 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3366. -/
theorem noS8R164_Law3366 : ∀ v : Magma.tup8R164,
    ¬ @Equation3366 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3366) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3366) (by native_decide) v.1 v.2
    ((@Law3366.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3367 takes them (10 nodes). -/
def ordS8R164_Law3367 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3367. -/
theorem noS8R164_Law3367 : ∀ v : Magma.tup8R164,
    ¬ @Equation3367 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3367) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3367) (by native_decide) v.1 v.2
    ((@Law3367.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3368 takes them (7 nodes). -/
def ordS8R164_Law3368 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3368. -/
theorem noS8R164_Law3368 : ∀ v : Magma.tup8R164,
    ¬ @Equation3368 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3368) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3368) (by native_decide) v.1 v.2
    ((@Law3368.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3369 takes them (6 nodes). -/
def ordS8R164_Law3369 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3369. -/
theorem noS8R164_Law3369 : ∀ v : Magma.tup8R164,
    ¬ @Equation3369 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3369) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3369) (by native_decide) v.1 v.2
    ((@Law3369.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3371 takes them (10 nodes). -/
def ordS8R164_Law3371 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3371. -/
theorem noS8R164_Law3371 : ∀ v : Magma.tup8R164,
    ¬ @Equation3371 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3371) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3371) (by native_decide) v.1 v.2
    ((@Law3371.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3372 takes them (7 nodes). -/
def ordS8R164_Law3372 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3372. -/
theorem noS8R164_Law3372 : ∀ v : Magma.tup8R164,
    ¬ @Equation3372 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3372) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3372) (by native_decide) v.1 v.2
    ((@Law3372.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3373 takes them (6 nodes). -/
def ordS8R164_Law3373 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3373. -/
theorem noS8R164_Law3373 : ∀ v : Magma.tup8R164,
    ¬ @Equation3373 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3373) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3373) (by native_decide) v.1 v.2
    ((@Law3373.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3374 takes them (7 nodes). -/
def ordS8R164_Law3374 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3374. -/
theorem noS8R164_Law3374 : ∀ v : Magma.tup8R164,
    ¬ @Equation3374 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3374) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3374) (by native_decide) v.1 v.2
    ((@Law3374.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3375 takes them (10 nodes). -/
def ordS8R164_Law3375 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3375. -/
theorem noS8R164_Law3375 : ∀ v : Magma.tup8R164,
    ¬ @Equation3375 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3375) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3375) (by native_decide) v.1 v.2
    ((@Law3375.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3376 takes them (7 nodes). -/
def ordS8R164_Law3376 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3376. -/
theorem noS8R164_Law3376 : ∀ v : Magma.tup8R164,
    ¬ @Equation3376 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3376) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3376) (by native_decide) v.1 v.2
    ((@Law3376.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3377 takes them (7 nodes). -/
def ordS8R164_Law3377 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3377. -/
theorem noS8R164_Law3377 : ∀ v : Magma.tup8R164,
    ¬ @Equation3377 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3377) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3377) (by native_decide) v.1 v.2
    ((@Law3377.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3378 takes them (6 nodes). -/
def ordS8R164_Law3378 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3378. -/
theorem noS8R164_Law3378 : ∀ v : Magma.tup8R164,
    ¬ @Equation3378 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3378) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3378) (by native_decide) v.1 v.2
    ((@Law3378.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3379 takes them (6 nodes). -/
def ordS8R164_Law3379 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3379. -/
theorem noS8R164_Law3379 : ∀ v : Magma.tup8R164,
    ¬ @Equation3379 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3379) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3379) (by native_decide) v.1 v.2
    ((@Law3379.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3380 takes them (10 nodes). -/
def ordS8R164_Law3380 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3380. -/
theorem noS8R164_Law3380 : ∀ v : Magma.tup8R164,
    ¬ @Equation3380 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3380) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3380) (by native_decide) v.1 v.2
    ((@Law3380.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3381 takes them (6 nodes). -/
def ordS8R164_Law3381 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3381. -/
theorem noS8R164_Law3381 : ∀ v : Magma.tup8R164,
    ¬ @Equation3381 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3381) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3381) (by native_decide) v.1 v.2
    ((@Law3381.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3382 takes them (6 nodes). -/
def ordS8R164_Law3382 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3382. -/
theorem noS8R164_Law3382 : ∀ v : Magma.tup8R164,
    ¬ @Equation3382 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3382) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3382) (by native_decide) v.1 v.2
    ((@Law3382.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3383 takes them (7 nodes). -/
def ordS8R164_Law3383 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3383. -/
theorem noS8R164_Law3383 : ∀ v : Magma.tup8R164,
    ¬ @Equation3383 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3383) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3383) (by native_decide) v.1 v.2
    ((@Law3383.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3384 takes them (10 nodes). -/
def ordS8R164_Law3384 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3384. -/
theorem noS8R164_Law3384 : ∀ v : Magma.tup8R164,
    ¬ @Equation3384 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3384) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3384) (by native_decide) v.1 v.2
    ((@Law3384.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3386 takes them (6 nodes). -/
def ordS8R164_Law3386 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3386. -/
theorem noS8R164_Law3386 : ∀ v : Magma.tup8R164,
    ¬ @Equation3386 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3386) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3386) (by native_decide) v.1 v.2
    ((@Law3386.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3387 takes them (6 nodes). -/
def ordS8R164_Law3387 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3387. -/
theorem noS8R164_Law3387 : ∀ v : Magma.tup8R164,
    ¬ @Equation3387 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3387) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3387) (by native_decide) v.1 v.2
    ((@Law3387.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3389 takes them (6 nodes). -/
def ordS8R164_Law3389 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3389. -/
theorem noS8R164_Law3389 : ∀ v : Magma.tup8R164,
    ¬ @Equation3389 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3389) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3389) (by native_decide) v.1 v.2
    ((@Law3389.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3390 takes them (6 nodes). -/
def ordS8R164_Law3390 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3390. -/
theorem noS8R164_Law3390 : ∀ v : Magma.tup8R164,
    ¬ @Equation3390 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3390) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3390) (by native_decide) v.1 v.2
    ((@Law3390.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3391 takes them (6 nodes). -/
def ordS8R164_Law3391 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3391. -/
theorem noS8R164_Law3391 : ∀ v : Magma.tup8R164,
    ¬ @Equation3391 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3391) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3391) (by native_decide) v.1 v.2
    ((@Law3391.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3392 takes them (10 nodes). -/
def ordS8R164_Law3392 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3392. -/
theorem noS8R164_Law3392 : ∀ v : Magma.tup8R164,
    ¬ @Equation3392 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3392) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3392) (by native_decide) v.1 v.2
    ((@Law3392.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3393 takes them (6 nodes). -/
def ordS8R164_Law3393 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3393. -/
theorem noS8R164_Law3393 : ∀ v : Magma.tup8R164,
    ¬ @Equation3393 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3393) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3393) (by native_decide) v.1 v.2
    ((@Law3393.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3394 takes them (6 nodes). -/
def ordS8R164_Law3394 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3394. -/
theorem noS8R164_Law3394 : ∀ v : Magma.tup8R164,
    ¬ @Equation3394 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3394) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3394) (by native_decide) v.1 v.2
    ((@Law3394.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3395 takes them (6 nodes). -/
def ordS8R164_Law3395 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3395. -/
theorem noS8R164_Law3395 : ∀ v : Magma.tup8R164,
    ¬ @Equation3395 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3395) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3395) (by native_decide) v.1 v.2
    ((@Law3395.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3396 takes them (7 nodes). -/
def ordS8R164_Law3396 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3396. -/
theorem noS8R164_Law3396 : ∀ v : Magma.tup8R164,
    ¬ @Equation3396 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3396) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3396) (by native_decide) v.1 v.2
    ((@Law3396.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3397 takes them (10 nodes). -/
def ordS8R164_Law3397 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3397. -/
theorem noS8R164_Law3397 : ∀ v : Magma.tup8R164,
    ¬ @Equation3397 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3397) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3397) (by native_decide) v.1 v.2
    ((@Law3397.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3399 takes them (6 nodes). -/
def ordS8R164_Law3399 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3399. -/
theorem noS8R164_Law3399 : ∀ v : Magma.tup8R164,
    ¬ @Equation3399 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3399) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3399) (by native_decide) v.1 v.2
    ((@Law3399.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3400 takes them (7 nodes). -/
def ordS8R164_Law3400 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3400. -/
theorem noS8R164_Law3400 : ∀ v : Magma.tup8R164,
    ¬ @Equation3400 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3400) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3400) (by native_decide) v.1 v.2
    ((@Law3400.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3401 takes them (10 nodes). -/
def ordS8R164_Law3401 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3401. -/
theorem noS8R164_Law3401 : ∀ v : Magma.tup8R164,
    ¬ @Equation3401 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3401) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3401) (by native_decide) v.1 v.2
    ((@Law3401.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3402 takes them (7 nodes). -/
def ordS8R164_Law3402 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3402. -/
theorem noS8R164_Law3402 : ∀ v : Magma.tup8R164,
    ¬ @Equation3402 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3402) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3402) (by native_decide) v.1 v.2
    ((@Law3402.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3403 takes them (6 nodes). -/
def ordS8R164_Law3403 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3403. -/
theorem noS8R164_Law3403 : ∀ v : Magma.tup8R164,
    ¬ @Equation3403 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3403) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3403) (by native_decide) v.1 v.2
    ((@Law3403.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3405 takes them (10 nodes). -/
def ordS8R164_Law3405 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3405. -/
theorem noS8R164_Law3405 : ∀ v : Magma.tup8R164,
    ¬ @Equation3405 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3405) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3405) (by native_decide) v.1 v.2
    ((@Law3405.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3406 takes them (7 nodes). -/
def ordS8R164_Law3406 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3406. -/
theorem noS8R164_Law3406 : ∀ v : Magma.tup8R164,
    ¬ @Equation3406 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3406) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3406) (by native_decide) v.1 v.2
    ((@Law3406.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3407 takes them (6 nodes). -/
def ordS8R164_Law3407 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3407. -/
theorem noS8R164_Law3407 : ∀ v : Magma.tup8R164,
    ¬ @Equation3407 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3407) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3407) (by native_decide) v.1 v.2
    ((@Law3407.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3408 takes them (7 nodes). -/
def ordS8R164_Law3408 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3408. -/
theorem noS8R164_Law3408 : ∀ v : Magma.tup8R164,
    ¬ @Equation3408 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3408) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3408) (by native_decide) v.1 v.2
    ((@Law3408.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3409 takes them (10 nodes). -/
def ordS8R164_Law3409 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3409. -/
theorem noS8R164_Law3409 : ∀ v : Magma.tup8R164,
    ¬ @Equation3409 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3409) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3409) (by native_decide) v.1 v.2
    ((@Law3409.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3410 takes them (7 nodes). -/
def ordS8R164_Law3410 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3410. -/
theorem noS8R164_Law3410 : ∀ v : Magma.tup8R164,
    ¬ @Equation3410 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3410) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3410) (by native_decide) v.1 v.2
    ((@Law3410.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3411 takes them (7 nodes). -/
def ordS8R164_Law3411 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3411. -/
theorem noS8R164_Law3411 : ∀ v : Magma.tup8R164,
    ¬ @Equation3411 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3411) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3411) (by native_decide) v.1 v.2
    ((@Law3411.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3412 takes them (6 nodes). -/
def ordS8R164_Law3412 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3412. -/
theorem noS8R164_Law3412 : ∀ v : Magma.tup8R164,
    ¬ @Equation3412 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3412) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3412) (by native_decide) v.1 v.2
    ((@Law3412.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3413 takes them (7 nodes). -/
def ordS8R164_Law3413 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3413. -/
theorem noS8R164_Law3413 : ∀ v : Magma.tup8R164,
    ¬ @Equation3413 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3413) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3413) (by native_decide) v.1 v.2
    ((@Law3413.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3415 takes them (6 nodes). -/
def ordS8R164_Law3415 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3415. -/
theorem noS8R164_Law3415 : ∀ v : Magma.tup8R164,
    ¬ @Equation3415 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3415) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3415) (by native_decide) v.1 v.2
    ((@Law3415.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3416 takes them (6 nodes). -/
def ordS8R164_Law3416 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3416. -/
theorem noS8R164_Law3416 : ∀ v : Magma.tup8R164,
    ¬ @Equation3416 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3416) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3416) (by native_decide) v.1 v.2
    ((@Law3416.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3418 takes them (10 nodes). -/
def ordS8R164_Law3418 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3418. -/
theorem noS8R164_Law3418 : ∀ v : Magma.tup8R164,
    ¬ @Equation3418 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3418) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3418) (by native_decide) v.1 v.2
    ((@Law3418.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3419 takes them (7 nodes). -/
def ordS8R164_Law3419 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3419. -/
theorem noS8R164_Law3419 : ∀ v : Magma.tup8R164,
    ¬ @Equation3419 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3419) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3419) (by native_decide) v.1 v.2
    ((@Law3419.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3420 takes them (6 nodes). -/
def ordS8R164_Law3420 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3420. -/
theorem noS8R164_Law3420 : ∀ v : Magma.tup8R164,
    ¬ @Equation3420 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3420) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3420) (by native_decide) v.1 v.2
    ((@Law3420.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3421 takes them (6 nodes). -/
def ordS8R164_Law3421 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3421. -/
theorem noS8R164_Law3421 : ∀ v : Magma.tup8R164,
    ¬ @Equation3421 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3421) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3421) (by native_decide) v.1 v.2
    ((@Law3421.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3422 takes them (10 nodes). -/
def ordS8R164_Law3422 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3422. -/
theorem noS8R164_Law3422 : ∀ v : Magma.tup8R164,
    ¬ @Equation3422 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3422) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3422) (by native_decide) v.1 v.2
    ((@Law3422.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3423 takes them (6 nodes). -/
def ordS8R164_Law3423 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3423. -/
theorem noS8R164_Law3423 : ∀ v : Magma.tup8R164,
    ¬ @Equation3423 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3423) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3423) (by native_decide) v.1 v.2
    ((@Law3423.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3424 takes them (6 nodes). -/
def ordS8R164_Law3424 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3424. -/
theorem noS8R164_Law3424 : ∀ v : Magma.tup8R164,
    ¬ @Equation3424 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3424) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3424) (by native_decide) v.1 v.2
    ((@Law3424.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3425 takes them (6 nodes). -/
def ordS8R164_Law3425 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3425. -/
theorem noS8R164_Law3425 : ∀ v : Magma.tup8R164,
    ¬ @Equation3425 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3425) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3425) (by native_decide) v.1 v.2
    ((@Law3425.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3426 takes them (10 nodes). -/
def ordS8R164_Law3426 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3426. -/
theorem noS8R164_Law3426 : ∀ v : Magma.tup8R164,
    ¬ @Equation3426 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3426) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3426) (by native_decide) v.1 v.2
    ((@Law3426.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3427 takes them (6 nodes). -/
def ordS8R164_Law3427 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3427. -/
theorem noS8R164_Law3427 : ∀ v : Magma.tup8R164,
    ¬ @Equation3427 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3427) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3427) (by native_decide) v.1 v.2
    ((@Law3427.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3428 takes them (6 nodes). -/
def ordS8R164_Law3428 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3428. -/
theorem noS8R164_Law3428 : ∀ v : Magma.tup8R164,
    ¬ @Equation3428 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3428) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3428) (by native_decide) v.1 v.2
    ((@Law3428.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3429 takes them (6 nodes). -/
def ordS8R164_Law3429 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3429. -/
theorem noS8R164_Law3429 : ∀ v : Magma.tup8R164,
    ¬ @Equation3429 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3429) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3429) (by native_decide) v.1 v.2
    ((@Law3429.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3430 takes them (6 nodes). -/
def ordS8R164_Law3430 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3430. -/
theorem noS8R164_Law3430 : ∀ v : Magma.tup8R164,
    ¬ @Equation3430 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3430) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3430) (by native_decide) v.1 v.2
    ((@Law3430.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `83` equations. -/
theorem srch8R164_refutes_4 :
    FamilyRefutes Magma.srch8R164 [
      3335, 3336, 3337, 3338, 3339, 3340, 3341, 3343, 3344, 3345, 3347, 3348, 3349, 3351, 3352,
      3354, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3365, 3366, 3367, 3368, 3369, 3371,
      3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3386, 3387,
      3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3399, 3400, 3401, 3402, 3403, 3405,
      3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3415, 3416, 3418, 3419, 3420, 3421, 3422,
      3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430
    ] :=
  ⟨noS8R164_Law3335, noS8R164_Law3336, noS8R164_Law3337, noS8R164_Law3338, noS8R164_Law3339, noS8R164_Law3340, noS8R164_Law3341, noS8R164_Law3343, noS8R164_Law3344, noS8R164_Law3345, noS8R164_Law3347, noS8R164_Law3348, noS8R164_Law3349, noS8R164_Law3351, noS8R164_Law3352, noS8R164_Law3354, noS8R164_Law3356, noS8R164_Law3357, noS8R164_Law3358, noS8R164_Law3359, noS8R164_Law3360, noS8R164_Law3361, noS8R164_Law3362, noS8R164_Law3363, noS8R164_Law3365, noS8R164_Law3366, noS8R164_Law3367, noS8R164_Law3368, noS8R164_Law3369, noS8R164_Law3371, noS8R164_Law3372, noS8R164_Law3373, noS8R164_Law3374, noS8R164_Law3375, noS8R164_Law3376, noS8R164_Law3377, noS8R164_Law3378, noS8R164_Law3379, noS8R164_Law3380, noS8R164_Law3381, noS8R164_Law3382, noS8R164_Law3383, noS8R164_Law3384, noS8R164_Law3386, noS8R164_Law3387, noS8R164_Law3389, noS8R164_Law3390, noS8R164_Law3391, noS8R164_Law3392, noS8R164_Law3393, noS8R164_Law3394, noS8R164_Law3395, noS8R164_Law3396, noS8R164_Law3397, noS8R164_Law3399, noS8R164_Law3400, noS8R164_Law3401, noS8R164_Law3402, noS8R164_Law3403, noS8R164_Law3405, noS8R164_Law3406, noS8R164_Law3407, noS8R164_Law3408, noS8R164_Law3409, noS8R164_Law3410, noS8R164_Law3411, noS8R164_Law3412, noS8R164_Law3413, noS8R164_Law3415, noS8R164_Law3416, noS8R164_Law3418, noS8R164_Law3419, noS8R164_Law3420, noS8R164_Law3421, noS8R164_Law3422, noS8R164_Law3423, noS8R164_Law3424, noS8R164_Law3425, noS8R164_Law3426, noS8R164_Law3427, noS8R164_Law3428, noS8R164_Law3429, noS8R164_Law3430⟩

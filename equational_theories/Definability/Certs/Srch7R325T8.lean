import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 9 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `25` equations here, 2,886 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4323 takes them (864 nodes). -/
def ordS7R325_Law4323 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4323. -/
theorem noS7R325_Law4323 : ∀ v : Magma.tup7R325,
    ¬ @Equation4323 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4326 takes them (10 nodes). -/
def ordS7R325_Law4326 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4326. -/
theorem noS7R325_Law4326 : ∀ v : Magma.tup7R325,
    ¬ @Equation4326 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4326) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4326) (by native_decide) v.1 v.2
    ((@Law4326.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4328 takes them (153 nodes). -/
def ordS7R325_Law4328 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4328. -/
theorem noS7R325_Law4328 : ∀ v : Magma.tup7R325,
    ¬ @Equation4328 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4328) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4328) (by native_decide) v.1 v.2
    ((@Law4328.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4329 takes them (10 nodes). -/
def ordS7R325_Law4329 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4329. -/
theorem noS7R325_Law4329 : ∀ v : Magma.tup7R325,
    ¬ @Equation4329 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4329) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4329) (by native_decide) v.1 v.2
    ((@Law4329.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4330 takes them (622 nodes). -/
def ordS7R325_Law4330 : List (Fin 9) := [3, 8, 0, 5, 4, 2, 1, 7, 6]

/-- No member of the class satisfies equation 4330. -/
theorem noS7R325_Law4330 : ∀ v : Magma.tup7R325,
    ¬ @Equation4330 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4330) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4330) (by native_decide) v.1 v.2
    ((@Law4330.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4333 takes them (10 nodes). -/
def ordS7R325_Law4333 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4333. -/
theorem noS7R325_Law4333 : ∀ v : Magma.tup7R325,
    ¬ @Equation4333 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4333) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4333) (by native_decide) v.1 v.2
    ((@Law4333.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4334 takes them (246 nodes). -/
def ordS7R325_Law4334 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4334. -/
theorem noS7R325_Law4334 : ∀ v : Magma.tup7R325,
    ¬ @Equation4334 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4334) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4334) (by native_decide) v.1 v.2
    ((@Law4334.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4335 takes them (16 nodes). -/
def ordS7R325_Law4335 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4335. -/
theorem noS7R325_Law4335 : ∀ v : Magma.tup7R325,
    ¬ @Equation4335 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4335) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4335) (by native_decide) v.1 v.2
    ((@Law4335.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4338 takes them (10 nodes). -/
def ordS7R325_Law4338 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4338. -/
theorem noS7R325_Law4338 : ∀ v : Magma.tup7R325,
    ¬ @Equation4338 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4338) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4338) (by native_decide) v.1 v.2
    ((@Law4338.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4340 takes them (100 nodes). -/
def ordS7R325_Law4340 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4340. -/
theorem noS7R325_Law4340 : ∀ v : Magma.tup7R325,
    ¬ @Equation4340 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4340) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4340) (by native_decide) v.1 v.2
    ((@Law4340.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4342 takes them (52 nodes). -/
def ordS7R325_Law4342 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4342. -/
theorem noS7R325_Law4342 : ∀ v : Magma.tup7R325,
    ¬ @Equation4342 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4342) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4342) (by native_decide) v.1 v.2
    ((@Law4342.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4344 takes them (10 nodes). -/
def ordS7R325_Law4344 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4344. -/
theorem noS7R325_Law4344 : ∀ v : Magma.tup7R325,
    ¬ @Equation4344 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4344) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4344) (by native_decide) v.1 v.2
    ((@Law4344.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4345 takes them (16 nodes). -/
def ordS7R325_Law4345 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4345. -/
theorem noS7R325_Law4345 : ∀ v : Magma.tup7R325,
    ¬ @Equation4345 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4345) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4345) (by native_decide) v.1 v.2
    ((@Law4345.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4347 takes them (10 nodes). -/
def ordS7R325_Law4347 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4347. -/
theorem noS7R325_Law4347 : ∀ v : Magma.tup7R325,
    ¬ @Equation4347 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4347) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4347) (by native_decide) v.1 v.2
    ((@Law4347.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4348 takes them (246 nodes). -/
def ordS7R325_Law4348 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4348. -/
theorem noS7R325_Law4348 : ∀ v : Magma.tup7R325,
    ¬ @Equation4348 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4349 takes them (10 nodes). -/
def ordS7R325_Law4349 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4349. -/
theorem noS7R325_Law4349 : ∀ v : Magma.tup7R325,
    ¬ @Equation4349 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4349) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4349) (by native_decide) v.1 v.2
    ((@Law4349.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4350 takes them (193 nodes). -/
def ordS7R325_Law4350 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4350. -/
theorem noS7R325_Law4350 : ∀ v : Magma.tup7R325,
    ¬ @Equation4350 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4350) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4350) (by native_decide) v.1 v.2
    ((@Law4350.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4352 takes them (10 nodes). -/
def ordS7R325_Law4352 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4352. -/
theorem noS7R325_Law4352 : ∀ v : Magma.tup7R325,
    ¬ @Equation4352 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4352) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4352) (by native_decide) v.1 v.2
    ((@Law4352.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4353 takes them (16 nodes). -/
def ordS7R325_Law4353 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4353. -/
theorem noS7R325_Law4353 : ∀ v : Magma.tup7R325,
    ¬ @Equation4353 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4353) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4353) (by native_decide) v.1 v.2
    ((@Law4353.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (58 nodes). -/
def ordS7R325_Law4354 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4354. -/
theorem noS7R325_Law4354 : ∀ v : Magma.tup7R325,
    ¬ @Equation4354 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4356 takes them (10 nodes). -/
def ordS7R325_Law4356 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4356. -/
theorem noS7R325_Law4356 : ∀ v : Magma.tup7R325,
    ¬ @Equation4356 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4356) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4356) (by native_decide) v.1 v.2
    ((@Law4356.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4359 takes them (52 nodes). -/
def ordS7R325_Law4359 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4359. -/
theorem noS7R325_Law4359 : ∀ v : Magma.tup7R325,
    ¬ @Equation4359 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4359) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4359) (by native_decide) v.1 v.2
    ((@Law4359.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4360 takes them (100 nodes). -/
def ordS7R325_Law4360 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4360. -/
theorem noS7R325_Law4360 : ∀ v : Magma.tup7R325,
    ¬ @Equation4360 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4360) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4360) (by native_decide) v.1 v.2
    ((@Law4360.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4361 takes them (52 nodes). -/
def ordS7R325_Law4361 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4361. -/
theorem noS7R325_Law4361 : ∀ v : Magma.tup7R325,
    ¬ @Equation4361 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4361) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4361) (by native_decide) v.1 v.2
    ((@Law4361.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4363 takes them (10 nodes). -/
def ordS7R325_Law4363 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4363. -/
theorem noS7R325_Law4363 : ∀ v : Magma.tup7R325,
    ¬ @Equation4363 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4363) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4363) (by native_decide) v.1 v.2
    ((@Law4363.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch7R325_refutes_8 :
    FamilyRefutes Magma.srch7R325 [
      4323, 4326, 4328, 4329, 4330, 4333, 4334, 4335, 4338, 4340, 4342, 4344, 4345, 4347, 4348,
      4349, 4350, 4352, 4353, 4354, 4356, 4359, 4360, 4361, 4363
    ] :=
  ⟨noS7R325_Law4323, noS7R325_Law4326, noS7R325_Law4328, noS7R325_Law4329, noS7R325_Law4330, noS7R325_Law4333, noS7R325_Law4334, noS7R325_Law4335, noS7R325_Law4338, noS7R325_Law4340, noS7R325_Law4342, noS7R325_Law4344, noS7R325_Law4345, noS7R325_Law4347, noS7R325_Law4348, noS7R325_Law4349, noS7R325_Law4350, noS7R325_Law4352, noS7R325_Law4353, noS7R325_Law4354, noS7R325_Law4356, noS7R325_Law4359, noS7R325_Law4360, noS7R325_Law4361, noS7R325_Law4363⟩

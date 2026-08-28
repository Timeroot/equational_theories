import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 49 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `21` equations here, 2,901 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4336 takes them (193 nodes). -/
def ordS7R12_Law4336 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4336. -/
theorem noS7R12_Law4336 : ∀ v : Magma.tup7R12,
    ¬ @Equation4336 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4336) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4336) (by native_decide) v.1 v.2
    ((@Law4336.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4337 takes them (148 nodes). -/
def ordS7R12_Law4337 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4337. -/
theorem noS7R12_Law4337 : ∀ v : Magma.tup7R12,
    ¬ @Equation4337 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4337) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4337) (by native_decide) v.1 v.2
    ((@Law4337.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (82 nodes). -/
def ordS7R12_Law4339 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4339. -/
theorem noS7R12_Law4339 : ∀ v : Magma.tup7R12,
    ¬ @Equation4339 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4340 takes them (76 nodes). -/
def ordS7R12_Law4340 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4340. -/
theorem noS7R12_Law4340 : ∀ v : Magma.tup7R12,
    ¬ @Equation4340 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4340) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4340) (by native_decide) v.1 v.2
    ((@Law4340.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4342 takes them (32 nodes). -/
def ordS7R12_Law4342 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4342. -/
theorem noS7R12_Law4342 : ∀ v : Magma.tup7R12,
    ¬ @Equation4342 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4342) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4342) (by native_decide) v.1 v.2
    ((@Law4342.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4348 takes them (42 nodes). -/
def ordS7R12_Law4348 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4348. -/
theorem noS7R12_Law4348 : ∀ v : Magma.tup7R12,
    ¬ @Equation4348 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (40 nodes). -/
def ordS7R12_Law4354 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4354. -/
theorem noS7R12_Law4354 : ∀ v : Magma.tup7R12,
    ¬ @Equation4354 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (76 nodes). -/
def ordS7R12_Law4357 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4357. -/
theorem noS7R12_Law4357 : ∀ v : Magma.tup7R12,
    ¬ @Equation4357 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (320 nodes). -/
def ordS7R12_Law4358 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4358. -/
theorem noS7R12_Law4358 : ∀ v : Magma.tup7R12,
    ¬ @Equation4358 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4359 takes them (32 nodes). -/
def ordS7R12_Law4359 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4359. -/
theorem noS7R12_Law4359 : ∀ v : Magma.tup7R12,
    ¬ @Equation4359 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4359) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4359) (by native_decide) v.1 v.2
    ((@Law4359.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4360 takes them (60 nodes). -/
def ordS7R12_Law4360 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4360. -/
theorem noS7R12_Law4360 : ∀ v : Magma.tup7R12,
    ¬ @Equation4360 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4360) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4360) (by native_decide) v.1 v.2
    ((@Law4360.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4361 takes them (28 nodes). -/
def ordS7R12_Law4361 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4361. -/
theorem noS7R12_Law4361 : ∀ v : Magma.tup7R12,
    ¬ @Equation4361 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4361) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 5)
    (ord := ordS7R12_Law4361) (by native_decide) v.1 v.2
    ((@Law4361.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (266 nodes). -/
def ordS7R12_Law4362 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4362. -/
theorem noS7R12_Law4362 : ∀ v : Magma.tup7R12,
    ¬ @Equation4362 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4367 takes them (22 nodes). -/
def ordS7R12_Law4367 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4367. -/
theorem noS7R12_Law4367 : ∀ v : Magma.tup7R12,
    ¬ @Equation4367 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4374 takes them (38 nodes). -/
def ordS7R12_Law4374 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4374. -/
theorem noS7R12_Law4374 : ∀ v : Magma.tup7R12,
    ¬ @Equation4374 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4374) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4374) (by native_decide) v.1 v.2
    ((@Law4374.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4378 takes them (22 nodes). -/
def ordS7R12_Law4378 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4378. -/
theorem noS7R12_Law4378 : ∀ v : Magma.tup7R12,
    ¬ @Equation4378 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4378) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 5)
    (ord := ordS7R12_Law4378) (by native_decide) v.1 v.2
    ((@Law4378.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4382 takes them (337 nodes). -/
def ordS7R12_Law4382 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4382. -/
theorem noS7R12_Law4382 : ∀ v : Magma.tup7R12,
    ¬ @Equation4382 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4382) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4382) (by native_decide) v.1 v.2
    ((@Law4382.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4386 takes them (240 nodes). -/
def ordS7R12_Law4386 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4386. -/
theorem noS7R12_Law4386 : ∀ v : Magma.tup7R12,
    ¬ @Equation4386 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4386) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4386) (by native_decide) v.1 v.2
    ((@Law4386.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4392 takes them (139 nodes). -/
def ordS7R12_Law4392 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4392. -/
theorem noS7R12_Law4392 : ∀ v : Magma.tup7R12,
    ¬ @Equation4392 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4392) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4392) (by native_decide) v.1 v.2
    ((@Law4392.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4398 takes them (620 nodes). -/
def ordS7R12_Law4398 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4398. -/
theorem noS7R12_Law4398 : ∀ v : Magma.tup7R12,
    ¬ @Equation4398 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (88 nodes). -/
def ordS7R12_Law4401 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4401. -/
theorem noS7R12_Law4401 : ∀ v : Magma.tup7R12,
    ¬ @Equation4401 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `21` equations. -/
theorem srch7R12_refutes_48 :
    FamilyRefutes Magma.srch7R12 [
      4336, 4337, 4339, 4340, 4342, 4348, 4354, 4357, 4358, 4359, 4360, 4361, 4362, 4367, 4374,
      4378, 4382, 4386, 4392, 4398, 4401
    ] :=
  ⟨noS7R12_Law4336, noS7R12_Law4337, noS7R12_Law4339, noS7R12_Law4340, noS7R12_Law4342, noS7R12_Law4348, noS7R12_Law4354, noS7R12_Law4357, noS7R12_Law4358, noS7R12_Law4359, noS7R12_Law4360, noS7R12_Law4361, noS7R12_Law4362, noS7R12_Law4367, noS7R12_Law4374, noS7R12_Law4378, noS7R12_Law4382, noS7R12_Law4386, noS7R12_Law4392, noS7R12_Law4398, noS7R12_Law4401⟩

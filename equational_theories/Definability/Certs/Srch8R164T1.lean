import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 2 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `77` equations here, 885 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 378 takes them (28 nodes). -/
def ordS8R164_Law378 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 378. -/
theorem noS8R164_Law378 : ∀ v : Magma.tup8R164,
    ¬ @Equation378 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law378) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law378) (by native_decide) v.1 v.2
    ((@Law378.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 379 takes them (9 nodes). -/
def ordS8R164_Law379 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 379. -/
theorem noS8R164_Law379 : ∀ v : Magma.tup8R164,
    ¬ @Equation379 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law379) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law379) (by native_decide) v.1 v.2
    ((@Law379.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 380 takes them (9 nodes). -/
def ordS8R164_Law380 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 380. -/
theorem noS8R164_Law380 : ∀ v : Magma.tup8R164,
    ¬ @Equation380 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law380) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law380) (by native_decide) v.1 v.2
    ((@Law380.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 381 takes them (13 nodes). -/
def ordS8R164_Law381 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 381. -/
theorem noS8R164_Law381 : ∀ v : Magma.tup8R164,
    ¬ @Equation381 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law381) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law381) (by native_decide) v.1 v.2
    ((@Law381.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 382 takes them (9 nodes). -/
def ordS8R164_Law382 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 382. -/
theorem noS8R164_Law382 : ∀ v : Magma.tup8R164,
    ¬ @Equation382 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law382) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law382) (by native_decide) v.1 v.2
    ((@Law382.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 383 takes them (9 nodes). -/
def ordS8R164_Law383 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 383. -/
theorem noS8R164_Law383 : ∀ v : Magma.tup8R164,
    ¬ @Equation383 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law383) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law383) (by native_decide) v.1 v.2
    ((@Law383.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 384 takes them (11 nodes). -/
def ordS8R164_Law384 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 384. -/
theorem noS8R164_Law384 : ∀ v : Magma.tup8R164,
    ¬ @Equation384 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law384) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law384) (by native_decide) v.1 v.2
    ((@Law384.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (17 nodes). -/
def ordS8R164_Law385 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 385. -/
theorem noS8R164_Law385 : ∀ v : Magma.tup8R164,
    ¬ @Equation385 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 386 takes them (6 nodes). -/
def ordS8R164_Law386 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 386. -/
theorem noS8R164_Law386 : ∀ v : Magma.tup8R164,
    ¬ @Equation386 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law386) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law386) (by native_decide) v.1 v.2
    ((@Law386.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 388 takes them (10 nodes). -/
def ordS8R164_Law388 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 388. -/
theorem noS8R164_Law388 : ∀ v : Magma.tup8R164,
    ¬ @Equation388 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law388) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law388) (by native_decide) v.1 v.2
    ((@Law388.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 389 takes them (6 nodes). -/
def ordS8R164_Law389 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 389. -/
theorem noS8R164_Law389 : ∀ v : Magma.tup8R164,
    ¬ @Equation389 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law389) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law389) (by native_decide) v.1 v.2
    ((@Law389.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 390 takes them (7 nodes). -/
def ordS8R164_Law390 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 390. -/
theorem noS8R164_Law390 : ∀ v : Magma.tup8R164,
    ¬ @Equation390 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law390) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law390) (by native_decide) v.1 v.2
    ((@Law390.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 391 takes them (10 nodes). -/
def ordS8R164_Law391 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 391. -/
theorem noS8R164_Law391 : ∀ v : Magma.tup8R164,
    ¬ @Equation391 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law391) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law391) (by native_decide) v.1 v.2
    ((@Law391.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 392 takes them (7 nodes). -/
def ordS8R164_Law392 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 392. -/
theorem noS8R164_Law392 : ∀ v : Magma.tup8R164,
    ¬ @Equation392 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law392) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law392) (by native_decide) v.1 v.2
    ((@Law392.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 393 takes them (6 nodes). -/
def ordS8R164_Law393 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 393. -/
theorem noS8R164_Law393 : ∀ v : Magma.tup8R164,
    ¬ @Equation393 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law393) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law393) (by native_decide) v.1 v.2
    ((@Law393.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 394 takes them (6 nodes). -/
def ordS8R164_Law394 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 394. -/
theorem noS8R164_Law394 : ∀ v : Magma.tup8R164,
    ¬ @Equation394 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law394) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law394) (by native_decide) v.1 v.2
    ((@Law394.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (10 nodes). -/
def ordS8R164_Law395 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 395. -/
theorem noS8R164_Law395 : ∀ v : Magma.tup8R164,
    ¬ @Equation395 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 396 takes them (6 nodes). -/
def ordS8R164_Law396 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 396. -/
theorem noS8R164_Law396 : ∀ v : Magma.tup8R164,
    ¬ @Equation396 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law396) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law396) (by native_decide) v.1 v.2
    ((@Law396.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 397 takes them (6 nodes). -/
def ordS8R164_Law397 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 397. -/
theorem noS8R164_Law397 : ∀ v : Magma.tup8R164,
    ¬ @Equation397 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law397) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law397) (by native_decide) v.1 v.2
    ((@Law397.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 398 takes them (7 nodes). -/
def ordS8R164_Law398 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 398. -/
theorem noS8R164_Law398 : ∀ v : Magma.tup8R164,
    ¬ @Equation398 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law398) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law398) (by native_decide) v.1 v.2
    ((@Law398.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 399 takes them (10 nodes). -/
def ordS8R164_Law399 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 399. -/
theorem noS8R164_Law399 : ∀ v : Magma.tup8R164,
    ¬ @Equation399 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law399) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law399) (by native_decide) v.1 v.2
    ((@Law399.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 400 takes them (7 nodes). -/
def ordS8R164_Law400 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 400. -/
theorem noS8R164_Law400 : ∀ v : Magma.tup8R164,
    ¬ @Equation400 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law400) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law400) (by native_decide) v.1 v.2
    ((@Law400.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 401 takes them (6 nodes). -/
def ordS8R164_Law401 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 401. -/
theorem noS8R164_Law401 : ∀ v : Magma.tup8R164,
    ¬ @Equation401 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law401) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law401) (by native_decide) v.1 v.2
    ((@Law401.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 402 takes them (6 nodes). -/
def ordS8R164_Law402 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 402. -/
theorem noS8R164_Law402 : ∀ v : Magma.tup8R164,
    ¬ @Equation402 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law402) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law402) (by native_decide) v.1 v.2
    ((@Law402.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 403 takes them (10 nodes). -/
def ordS8R164_Law403 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 403. -/
theorem noS8R164_Law403 : ∀ v : Magma.tup8R164,
    ¬ @Equation403 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law403) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law403) (by native_decide) v.1 v.2
    ((@Law403.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 404 takes them (6 nodes). -/
def ordS8R164_Law404 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 404. -/
theorem noS8R164_Law404 : ∀ v : Magma.tup8R164,
    ¬ @Equation404 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law404) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law404) (by native_decide) v.1 v.2
    ((@Law404.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 405 takes them (6 nodes). -/
def ordS8R164_Law405 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 405. -/
theorem noS8R164_Law405 : ∀ v : Magma.tup8R164,
    ¬ @Equation405 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law405) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law405) (by native_decide) v.1 v.2
    ((@Law405.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 406 takes them (6 nodes). -/
def ordS8R164_Law406 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 406. -/
theorem noS8R164_Law406 : ∀ v : Magma.tup8R164,
    ¬ @Equation406 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law406) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law406) (by native_decide) v.1 v.2
    ((@Law406.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 407 takes them (10 nodes). -/
def ordS8R164_Law407 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 407. -/
theorem noS8R164_Law407 : ∀ v : Magma.tup8R164,
    ¬ @Equation407 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law407) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law407) (by native_decide) v.1 v.2
    ((@Law407.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 408 takes them (6 nodes). -/
def ordS8R164_Law408 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 408. -/
theorem noS8R164_Law408 : ∀ v : Magma.tup8R164,
    ¬ @Equation408 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law408) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law408) (by native_decide) v.1 v.2
    ((@Law408.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 409 takes them (6 nodes). -/
def ordS8R164_Law409 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 409. -/
theorem noS8R164_Law409 : ∀ v : Magma.tup8R164,
    ¬ @Equation409 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law409) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law409) (by native_decide) v.1 v.2
    ((@Law409.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 410 takes them (6 nodes). -/
def ordS8R164_Law410 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 410. -/
theorem noS8R164_Law410 : ∀ v : Magma.tup8R164,
    ¬ @Equation410 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law410) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law410) (by native_decide) v.1 v.2
    ((@Law410.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 413 takes them (16 nodes). -/
def ordS8R164_Law413 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 413. -/
theorem noS8R164_Law413 : ∀ v : Magma.tup8R164,
    ¬ @Equation413 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law413) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law413) (by native_decide) v.1 v.2
    ((@Law413.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 426 takes them (17 nodes). -/
def ordS8R164_Law426 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 426. -/
theorem noS8R164_Law426 : ∀ v : Magma.tup8R164,
    ¬ @Equation426 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law426) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law426) (by native_decide) v.1 v.2
    ((@Law426.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 432 takes them (16 nodes). -/
def ordS8R164_Law432 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 432. -/
theorem noS8R164_Law432 : ∀ v : Magma.tup8R164,
    ¬ @Equation432 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law432) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law432) (by native_decide) v.1 v.2
    ((@Law432.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 433 takes them (10 nodes). -/
def ordS8R164_Law433 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 433. -/
theorem noS8R164_Law433 : ∀ v : Magma.tup8R164,
    ¬ @Equation433 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law433) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law433) (by native_decide) v.1 v.2
    ((@Law433.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 434 takes them (10 nodes). -/
def ordS8R164_Law434 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 434. -/
theorem noS8R164_Law434 : ∀ v : Magma.tup8R164,
    ¬ @Equation434 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law434) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law434) (by native_decide) v.1 v.2
    ((@Law434.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 437 takes them (11 nodes). -/
def ordS8R164_Law437 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 437. -/
theorem noS8R164_Law437 : ∀ v : Magma.tup8R164,
    ¬ @Equation437 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law437) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law437) (by native_decide) v.1 v.2
    ((@Law437.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 439 takes them (16 nodes). -/
def ordS8R164_Law439 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 439. -/
theorem noS8R164_Law439 : ∀ v : Magma.tup8R164,
    ¬ @Equation439 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 442 takes them (14 nodes). -/
def ordS8R164_Law442 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 442. -/
theorem noS8R164_Law442 : ∀ v : Magma.tup8R164,
    ¬ @Equation442 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law442) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law442) (by native_decide) v.1 v.2
    ((@Law442.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 443 takes them (10 nodes). -/
def ordS8R164_Law443 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 443. -/
theorem noS8R164_Law443 : ∀ v : Magma.tup8R164,
    ¬ @Equation443 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law443) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law443) (by native_decide) v.1 v.2
    ((@Law443.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 832 takes them (18 nodes). -/
def ordS8R164_Law832 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 832. -/
theorem noS8R164_Law832 : ∀ v : Magma.tup8R164,
    ¬ @Equation832 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law832) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law832) (by native_decide) v.1 v.2
    ((@Law832.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (10 nodes). -/
def ordS8R164_Law834 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 834. -/
theorem noS8R164_Law834 : ∀ v : Magma.tup8R164,
    ¬ @Equation834 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (10 nodes). -/
def ordS8R164_Law837 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 837. -/
theorem noS8R164_Law837 : ∀ v : Magma.tup8R164,
    ¬ @Equation837 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 838 takes them (16 nodes). -/
def ordS8R164_Law838 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 838. -/
theorem noS8R164_Law838 : ∀ v : Magma.tup8R164,
    ¬ @Equation838 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law838) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law838) (by native_decide) v.1 v.2
    ((@Law838.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 839 takes them (11 nodes). -/
def ordS8R164_Law839 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 839. -/
theorem noS8R164_Law839 : ∀ v : Magma.tup8R164,
    ¬ @Equation839 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law839) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law839) (by native_decide) v.1 v.2
    ((@Law839.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 840 takes them (11 nodes). -/
def ordS8R164_Law840 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 840. -/
theorem noS8R164_Law840 : ∀ v : Magma.tup8R164,
    ¬ @Equation840 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law840) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law840) (by native_decide) v.1 v.2
    ((@Law840.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 841 takes them (10 nodes). -/
def ordS8R164_Law841 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 841. -/
theorem noS8R164_Law841 : ∀ v : Magma.tup8R164,
    ¬ @Equation841 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law841) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law841) (by native_decide) v.1 v.2
    ((@Law841.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 854 takes them (10 nodes). -/
def ordS8R164_Law854 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 854. -/
theorem noS8R164_Law854 : ∀ v : Magma.tup8R164,
    ¬ @Equation854 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law854) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law854) (by native_decide) v.1 v.2
    ((@Law854.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1022 takes them (17 nodes). -/
def ordS8R164_Law1022 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1022. -/
theorem noS8R164_Law1022 : ∀ v : Magma.tup8R164,
    ¬ @Equation1022 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1022) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1022) (by native_decide) v.1 v.2
    ((@Law1022.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1025 takes them (18 nodes). -/
def ordS8R164_Law1025 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1025. -/
theorem noS8R164_Law1025 : ∀ v : Magma.tup8R164,
    ¬ @Equation1025 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (17 nodes). -/
def ordS8R164_Law1031 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1031. -/
theorem noS8R164_Law1031 : ∀ v : Magma.tup8R164,
    ¬ @Equation1031 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1035 takes them (18 nodes). -/
def ordS8R164_Law1035 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1035. -/
theorem noS8R164_Law1035 : ∀ v : Magma.tup8R164,
    ¬ @Equation1035 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1035) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1035) (by native_decide) v.1 v.2
    ((@Law1035.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1039 takes them (12 nodes). -/
def ordS8R164_Law1039 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1039. -/
theorem noS8R164_Law1039 : ∀ v : Magma.tup8R164,
    ¬ @Equation1039 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1041 takes them (17 nodes). -/
def ordS8R164_Law1041 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1041. -/
theorem noS8R164_Law1041 : ∀ v : Magma.tup8R164,
    ¬ @Equation1041 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1041) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1041) (by native_decide) v.1 v.2
    ((@Law1041.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1042 takes them (10 nodes). -/
def ordS8R164_Law1042 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1042. -/
theorem noS8R164_Law1042 : ∀ v : Magma.tup8R164,
    ¬ @Equation1042 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1042) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1042) (by native_decide) v.1 v.2
    ((@Law1042.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1043 takes them (10 nodes). -/
def ordS8R164_Law1043 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1043. -/
theorem noS8R164_Law1043 : ∀ v : Magma.tup8R164,
    ¬ @Equation1043 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1043) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1043) (by native_decide) v.1 v.2
    ((@Law1043.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (11 nodes). -/
def ordS8R164_Law1046 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1046. -/
theorem noS8R164_Law1046 : ∀ v : Magma.tup8R164,
    ¬ @Equation1046 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1048 takes them (17 nodes). -/
def ordS8R164_Law1048 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1048. -/
theorem noS8R164_Law1048 : ∀ v : Magma.tup8R164,
    ¬ @Equation1048 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1048) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1048) (by native_decide) v.1 v.2
    ((@Law1048.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1051 takes them (16 nodes). -/
def ordS8R164_Law1051 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1051. -/
theorem noS8R164_Law1051 : ∀ v : Magma.tup8R164,
    ¬ @Equation1051 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1051) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1051) (by native_decide) v.1 v.2
    ((@Law1051.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1052 takes them (10 nodes). -/
def ordS8R164_Law1052 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1052. -/
theorem noS8R164_Law1052 : ∀ v : Magma.tup8R164,
    ¬ @Equation1052 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1052) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1052) (by native_decide) v.1 v.2
    ((@Law1052.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1055 takes them (17 nodes). -/
def ordS8R164_Law1055 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1055. -/
theorem noS8R164_Law1055 : ∀ v : Magma.tup8R164,
    ¬ @Equation1055 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1055) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1055) (by native_decide) v.1 v.2
    ((@Law1055.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1056 takes them (10 nodes). -/
def ordS8R164_Law1056 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1056. -/
theorem noS8R164_Law1056 : ∀ v : Magma.tup8R164,
    ¬ @Equation1056 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1056) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1056) (by native_decide) v.1 v.2
    ((@Law1056.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1059 takes them (16 nodes). -/
def ordS8R164_Law1059 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1059. -/
theorem noS8R164_Law1059 : ∀ v : Magma.tup8R164,
    ¬ @Equation1059 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1059) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1059) (by native_decide) v.1 v.2
    ((@Law1059.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1060 takes them (11 nodes). -/
def ordS8R164_Law1060 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1060. -/
theorem noS8R164_Law1060 : ∀ v : Magma.tup8R164,
    ¬ @Equation1060 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1060) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1060) (by native_decide) v.1 v.2
    ((@Law1060.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1063 takes them (16 nodes). -/
def ordS8R164_Law1063 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1063. -/
theorem noS8R164_Law1063 : ∀ v : Magma.tup8R164,
    ¬ @Equation1063 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1063) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1063) (by native_decide) v.1 v.2
    ((@Law1063.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1067 takes them (16 nodes). -/
def ordS8R164_Law1067 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1067. -/
theorem noS8R164_Law1067 : ∀ v : Magma.tup8R164,
    ¬ @Equation1067 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1067) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1067) (by native_decide) v.1 v.2
    ((@Law1067.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1068 takes them (10 nodes). -/
def ordS8R164_Law1068 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1068. -/
theorem noS8R164_Law1068 : ∀ v : Magma.tup8R164,
    ¬ @Equation1068 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1068) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1068) (by native_decide) v.1 v.2
    ((@Law1068.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1228 takes them (18 nodes). -/
def ordS8R164_Law1228 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1228. -/
theorem noS8R164_Law1228 : ∀ v : Magma.tup8R164,
    ¬ @Equation1228 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1228) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1228) (by native_decide) v.1 v.2
    ((@Law1228.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1230 takes them (10 nodes). -/
def ordS8R164_Law1230 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1230. -/
theorem noS8R164_Law1230 : ∀ v : Magma.tup8R164,
    ¬ @Equation1230 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1230) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1230) (by native_decide) v.1 v.2
    ((@Law1230.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1234 takes them (16 nodes). -/
def ordS8R164_Law1234 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1234. -/
theorem noS8R164_Law1234 : ∀ v : Magma.tup8R164,
    ¬ @Equation1234 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1234) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1234) (by native_decide) v.1 v.2
    ((@Law1234.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1238 takes them (18 nodes). -/
def ordS8R164_Law1238 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1238. -/
theorem noS8R164_Law1238 : ∀ v : Magma.tup8R164,
    ¬ @Equation1238 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1238) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1238) (by native_decide) v.1 v.2
    ((@Law1238.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1240 takes them (11 nodes). -/
def ordS8R164_Law1240 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1240. -/
theorem noS8R164_Law1240 : ∀ v : Magma.tup8R164,
    ¬ @Equation1240 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1240) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1240) (by native_decide) v.1 v.2
    ((@Law1240.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (13 nodes). -/
def ordS8R164_Law1242 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1242. -/
theorem noS8R164_Law1242 : ∀ v : Magma.tup8R164,
    ¬ @Equation1242 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1243 takes them (10 nodes). -/
def ordS8R164_Law1243 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1243. -/
theorem noS8R164_Law1243 : ∀ v : Magma.tup8R164,
    ¬ @Equation1243 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1243) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1243) (by native_decide) v.1 v.2
    ((@Law1243.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1244 takes them (16 nodes). -/
def ordS8R164_Law1244 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1244. -/
theorem noS8R164_Law1244 : ∀ v : Magma.tup8R164,
    ¬ @Equation1244 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1244) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1244) (by native_decide) v.1 v.2
    ((@Law1244.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1245 takes them (11 nodes). -/
def ordS8R164_Law1245 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1245. -/
theorem noS8R164_Law1245 : ∀ v : Magma.tup8R164,
    ¬ @Equation1245 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1245) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1245) (by native_decide) v.1 v.2
    ((@Law1245.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `77` equations. -/
theorem srch8R164_refutes_1 :
    FamilyRefutes Magma.srch8R164 [
      378, 379, 380, 381, 382, 383, 384, 385, 386, 388, 389, 390, 391, 392, 393, 394, 395, 396,
      397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 413, 426, 432, 433,
      434, 437, 439, 442, 443, 832, 834, 837, 838, 839, 840, 841, 854, 1022, 1025, 1031, 1035,
      1039, 1041, 1042, 1043, 1046, 1048, 1051, 1052, 1055, 1056, 1059, 1060, 1063, 1067, 1068,
      1228, 1230, 1234, 1238, 1240, 1242, 1243, 1244, 1245
    ] :=
  ⟨noS8R164_Law378, noS8R164_Law379, noS8R164_Law380, noS8R164_Law381, noS8R164_Law382, noS8R164_Law383, noS8R164_Law384, noS8R164_Law385, noS8R164_Law386, noS8R164_Law388, noS8R164_Law389, noS8R164_Law390, noS8R164_Law391, noS8R164_Law392, noS8R164_Law393, noS8R164_Law394, noS8R164_Law395, noS8R164_Law396, noS8R164_Law397, noS8R164_Law398, noS8R164_Law399, noS8R164_Law400, noS8R164_Law401, noS8R164_Law402, noS8R164_Law403, noS8R164_Law404, noS8R164_Law405, noS8R164_Law406, noS8R164_Law407, noS8R164_Law408, noS8R164_Law409, noS8R164_Law410, noS8R164_Law413, noS8R164_Law426, noS8R164_Law432, noS8R164_Law433, noS8R164_Law434, noS8R164_Law437, noS8R164_Law439, noS8R164_Law442, noS8R164_Law443, noS8R164_Law832, noS8R164_Law834, noS8R164_Law837, noS8R164_Law838, noS8R164_Law839, noS8R164_Law840, noS8R164_Law841, noS8R164_Law854, noS8R164_Law1022, noS8R164_Law1025, noS8R164_Law1031, noS8R164_Law1035, noS8R164_Law1039, noS8R164_Law1041, noS8R164_Law1042, noS8R164_Law1043, noS8R164_Law1046, noS8R164_Law1048, noS8R164_Law1051, noS8R164_Law1052, noS8R164_Law1055, noS8R164_Law1056, noS8R164_Law1059, noS8R164_Law1060, noS8R164_Law1063, noS8R164_Law1067, noS8R164_Law1068, noS8R164_Law1228, noS8R164_Law1230, noS8R164_Law1234, noS8R164_Law1238, noS8R164_Law1240, noS8R164_Law1242, noS8R164_Law1243, noS8R164_Law1244, noS8R164_Law1245⟩

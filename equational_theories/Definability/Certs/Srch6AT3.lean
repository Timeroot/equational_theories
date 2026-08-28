import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 4 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `34`
equations here, 2,502 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 347 takes them (173 nodes). -/
def ordS6A_Law347 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 347. -/
theorem noS6A_Law347 : ∀ v : Magma.tupS6A,
    ¬ @Equation347 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law347) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law347) (by native_decide) v.1 v.2
    ((@Law347.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 348 takes them (47 nodes). -/
def ordS6A_Law348 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 348. -/
theorem noS6A_Law348 : ∀ v : Magma.tupS6A,
    ¬ @Equation348 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law348) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law348) (by native_decide) v.1 v.2
    ((@Law348.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 349 takes them (26 nodes). -/
def ordS6A_Law349 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 349. -/
theorem noS6A_Law349 : ∀ v : Magma.tupS6A,
    ¬ @Equation349 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law349) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law349) (by native_decide) v.1 v.2
    ((@Law349.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 350 takes them (14 nodes). -/
def ordS6A_Law350 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 350. -/
theorem noS6A_Law350 : ∀ v : Magma.tupS6A,
    ¬ @Equation350 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law350) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law350) (by native_decide) v.1 v.2
    ((@Law350.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 351 takes them (39 nodes). -/
def ordS6A_Law351 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 351. -/
theorem noS6A_Law351 : ∀ v : Magma.tupS6A,
    ¬ @Equation351 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law351) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law351) (by native_decide) v.1 v.2
    ((@Law351.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 352 takes them (12 nodes). -/
def ordS6A_Law352 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 352. -/
theorem noS6A_Law352 : ∀ v : Magma.tupS6A,
    ¬ @Equation352 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law352) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law352) (by native_decide) v.1 v.2
    ((@Law352.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 353 takes them (12 nodes). -/
def ordS6A_Law353 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 353. -/
theorem noS6A_Law353 : ∀ v : Magma.tupS6A,
    ¬ @Equation353 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law353) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law353) (by native_decide) v.1 v.2
    ((@Law353.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 354 takes them (14 nodes). -/
def ordS6A_Law354 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 354. -/
theorem noS6A_Law354 : ∀ v : Magma.tupS6A,
    ¬ @Equation354 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law354) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law354) (by native_decide) v.1 v.2
    ((@Law354.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 355 takes them (39 nodes). -/
def ordS6A_Law355 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 355. -/
theorem noS6A_Law355 : ∀ v : Magma.tupS6A,
    ¬ @Equation355 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law355) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law355) (by native_decide) v.1 v.2
    ((@Law355.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 356 takes them (12 nodes). -/
def ordS6A_Law356 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 356. -/
theorem noS6A_Law356 : ∀ v : Magma.tupS6A,
    ¬ @Equation356 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law356) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law356) (by native_decide) v.1 v.2
    ((@Law356.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 357 takes them (12 nodes). -/
def ordS6A_Law357 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 357. -/
theorem noS6A_Law357 : ∀ v : Magma.tupS6A,
    ¬ @Equation357 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law357) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law357) (by native_decide) v.1 v.2
    ((@Law357.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 358 takes them (12 nodes). -/
def ordS6A_Law358 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 358. -/
theorem noS6A_Law358 : ∀ v : Magma.tupS6A,
    ¬ @Equation358 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law358) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law358) (by native_decide) v.1 v.2
    ((@Law358.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 374 takes them (191 nodes). -/
def ordS6A_Law374 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 374. -/
theorem noS6A_Law374 : ∀ v : Magma.tupS6A,
    ¬ @Equation374 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law374) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law374) (by native_decide) v.1 v.2
    ((@Law374.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 376 takes them (155 nodes). -/
def ordS6A_Law376 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 376. -/
theorem noS6A_Law376 : ∀ v : Magma.tupS6A,
    ¬ @Equation376 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law376) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law376) (by native_decide) v.1 v.2
    ((@Law376.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 380 takes them (51 nodes). -/
def ordS6A_Law380 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 380. -/
theorem noS6A_Law380 : ∀ v : Magma.tupS6A,
    ¬ @Equation380 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law380) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law380) (by native_decide) v.1 v.2
    ((@Law380.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 381 takes them (208 nodes). -/
def ordS6A_Law381 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 381. -/
theorem noS6A_Law381 : ∀ v : Magma.tupS6A,
    ¬ @Equation381 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law381) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law381) (by native_decide) v.1 v.2
    ((@Law381.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 382 takes them (41 nodes). -/
def ordS6A_Law382 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 382. -/
theorem noS6A_Law382 : ∀ v : Magma.tupS6A,
    ¬ @Equation382 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law382) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law382) (by native_decide) v.1 v.2
    ((@Law382.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 383 takes them (41 nodes). -/
def ordS6A_Law383 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 383. -/
theorem noS6A_Law383 : ∀ v : Magma.tupS6A,
    ¬ @Equation383 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law383) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law383) (by native_decide) v.1 v.2
    ((@Law383.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 384 takes them (166 nodes). -/
def ordS6A_Law384 : List (Fin 11) := [5, 3, 10, 0, 9, 6, 7, 8, 2, 4, 1]

/-- No member of the class satisfies equation 384. -/
theorem noS6A_Law384 : ∀ v : Magma.tupS6A,
    ¬ @Equation384 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law384) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law384) (by native_decide) v.1 v.2
    ((@Law384.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 386 takes them (110 nodes). -/
def ordS6A_Law386 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 386. -/
theorem noS6A_Law386 : ∀ v : Magma.tupS6A,
    ¬ @Equation386 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law386) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law386) (by native_decide) v.1 v.2
    ((@Law386.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 388 takes them (295 nodes). -/
def ordS6A_Law388 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 388. -/
theorem noS6A_Law388 : ∀ v : Magma.tupS6A,
    ¬ @Equation388 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law388) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law388) (by native_decide) v.1 v.2
    ((@Law388.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 389 takes them (128 nodes). -/
def ordS6A_Law389 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 389. -/
theorem noS6A_Law389 : ∀ v : Magma.tupS6A,
    ¬ @Equation389 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law389) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law389) (by native_decide) v.1 v.2
    ((@Law389.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 390 takes them (73 nodes). -/
def ordS6A_Law390 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 390. -/
theorem noS6A_Law390 : ∀ v : Magma.tupS6A,
    ¬ @Equation390 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law390) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law390) (by native_decide) v.1 v.2
    ((@Law390.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 391 takes them (133 nodes). -/
def ordS6A_Law391 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 391. -/
theorem noS6A_Law391 : ∀ v : Magma.tupS6A,
    ¬ @Equation391 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law391) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law391) (by native_decide) v.1 v.2
    ((@Law391.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 392 takes them (35 nodes). -/
def ordS6A_Law392 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 392. -/
theorem noS6A_Law392 : ∀ v : Magma.tupS6A,
    ¬ @Equation392 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law392) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law392) (by native_decide) v.1 v.2
    ((@Law392.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 393 takes them (30 nodes). -/
def ordS6A_Law393 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 393. -/
theorem noS6A_Law393 : ∀ v : Magma.tupS6A,
    ¬ @Equation393 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law393) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law393) (by native_decide) v.1 v.2
    ((@Law393.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 394 takes them (55 nodes). -/
def ordS6A_Law394 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 394. -/
theorem noS6A_Law394 : ∀ v : Magma.tupS6A,
    ¬ @Equation394 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law394) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law394) (by native_decide) v.1 v.2
    ((@Law394.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 396 takes them (55 nodes). -/
def ordS6A_Law396 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 396. -/
theorem noS6A_Law396 : ∀ v : Magma.tupS6A,
    ¬ @Equation396 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law396) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law396) (by native_decide) v.1 v.2
    ((@Law396.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 397 takes them (55 nodes). -/
def ordS6A_Law397 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 397. -/
theorem noS6A_Law397 : ∀ v : Magma.tupS6A,
    ¬ @Equation397 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law397) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law397) (by native_decide) v.1 v.2
    ((@Law397.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 398 takes them (37 nodes). -/
def ordS6A_Law398 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 398. -/
theorem noS6A_Law398 : ∀ v : Magma.tupS6A,
    ¬ @Equation398 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law398) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law398) (by native_decide) v.1 v.2
    ((@Law398.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 399 takes them (75 nodes). -/
def ordS6A_Law399 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 399. -/
theorem noS6A_Law399 : ∀ v : Magma.tupS6A,
    ¬ @Equation399 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law399) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law399) (by native_decide) v.1 v.2
    ((@Law399.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 400 takes them (32 nodes). -/
def ordS6A_Law400 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 400. -/
theorem noS6A_Law400 : ∀ v : Magma.tupS6A,
    ¬ @Equation400 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law400) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law400) (by native_decide) v.1 v.2
    ((@Law400.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 401 takes them (27 nodes). -/
def ordS6A_Law401 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 401. -/
theorem noS6A_Law401 : ∀ v : Magma.tupS6A,
    ¬ @Equation401 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law401) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law401) (by native_decide) v.1 v.2
    ((@Law401.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 402 takes them (97 nodes). -/
def ordS6A_Law402 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 402. -/
theorem noS6A_Law402 : ∀ v : Magma.tupS6A,
    ¬ @Equation402 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law402) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law402) (by native_decide) v.1 v.2
    ((@Law402.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `34` equations. -/
theorem srch6A_refutes_3 :
    FamilyRefutes Magma.srch6A [
      347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 374, 376, 380, 381, 382, 383,
      384, 386, 388, 389, 390, 391, 392, 393, 394, 396, 397, 398, 399, 400, 401, 402
    ] :=
  ⟨noS6A_Law347, noS6A_Law348, noS6A_Law349, noS6A_Law350, noS6A_Law351, noS6A_Law352, noS6A_Law353, noS6A_Law354, noS6A_Law355, noS6A_Law356, noS6A_Law357, noS6A_Law358, noS6A_Law374, noS6A_Law376, noS6A_Law380, noS6A_Law381, noS6A_Law382, noS6A_Law383, noS6A_Law384, noS6A_Law386, noS6A_Law388, noS6A_Law389, noS6A_Law390, noS6A_Law391, noS6A_Law392, noS6A_Law393, noS6A_Law394, noS6A_Law396, noS6A_Law397, noS6A_Law398, noS6A_Law399, noS6A_Law400, noS6A_Law401, noS6A_Law402⟩

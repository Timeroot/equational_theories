import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 34 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `45`
equations here, 2,137 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3404 takes them (129 nodes). -/
def ordS6A_Law3404 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3404. -/
theorem noS6A_Law3404 : ∀ v : Magma.tupS6A,
    ¬ @Equation3404 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3404) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3404) (by native_decide) v.1 v.2
    ((@Law3404.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3405 takes them (135 nodes). -/
def ordS6A_Law3405 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3405. -/
theorem noS6A_Law3405 : ∀ v : Magma.tupS6A,
    ¬ @Equation3405 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3405) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3405) (by native_decide) v.1 v.2
    ((@Law3405.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3406 takes them (78 nodes). -/
def ordS6A_Law3406 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3406. -/
theorem noS6A_Law3406 : ∀ v : Magma.tupS6A,
    ¬ @Equation3406 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3406) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3406) (by native_decide) v.1 v.2
    ((@Law3406.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3407 takes them (26 nodes). -/
def ordS6A_Law3407 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3407. -/
theorem noS6A_Law3407 : ∀ v : Magma.tupS6A,
    ¬ @Equation3407 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3407) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3407) (by native_decide) v.1 v.2
    ((@Law3407.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3408 takes them (66 nodes). -/
def ordS6A_Law3408 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3408. -/
theorem noS6A_Law3408 : ∀ v : Magma.tupS6A,
    ¬ @Equation3408 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3408) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3408) (by native_decide) v.1 v.2
    ((@Law3408.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3409 takes them (135 nodes). -/
def ordS6A_Law3409 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3409. -/
theorem noS6A_Law3409 : ∀ v : Magma.tupS6A,
    ¬ @Equation3409 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3409) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3409) (by native_decide) v.1 v.2
    ((@Law3409.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3410 takes them (78 nodes). -/
def ordS6A_Law3410 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3410. -/
theorem noS6A_Law3410 : ∀ v : Magma.tupS6A,
    ¬ @Equation3410 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3410) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3410) (by native_decide) v.1 v.2
    ((@Law3410.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3411 takes them (78 nodes). -/
def ordS6A_Law3411 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3411. -/
theorem noS6A_Law3411 : ∀ v : Magma.tupS6A,
    ¬ @Equation3411 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3411) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3411) (by native_decide) v.1 v.2
    ((@Law3411.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3412 takes them (26 nodes). -/
def ordS6A_Law3412 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3412. -/
theorem noS6A_Law3412 : ∀ v : Magma.tupS6A,
    ¬ @Equation3412 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3412) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3412) (by native_decide) v.1 v.2
    ((@Law3412.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3413 takes them (37 nodes). -/
def ordS6A_Law3413 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3413. -/
theorem noS6A_Law3413 : ∀ v : Magma.tupS6A,
    ¬ @Equation3413 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3413) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3413) (by native_decide) v.1 v.2
    ((@Law3413.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3415 takes them (14 nodes). -/
def ordS6A_Law3415 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3415. -/
theorem noS6A_Law3415 : ∀ v : Magma.tupS6A,
    ¬ @Equation3415 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3415) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3415) (by native_decide) v.1 v.2
    ((@Law3415.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3416 takes them (14 nodes). -/
def ordS6A_Law3416 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3416. -/
theorem noS6A_Law3416 : ∀ v : Magma.tupS6A,
    ¬ @Equation3416 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3416) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3416) (by native_decide) v.1 v.2
    ((@Law3416.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3417 takes them (172 nodes). -/
def ordS6A_Law3417 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3417. -/
theorem noS6A_Law3417 : ∀ v : Magma.tupS6A,
    ¬ @Equation3417 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3417) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3417) (by native_decide) v.1 v.2
    ((@Law3417.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3418 takes them (191 nodes). -/
def ordS6A_Law3418 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3418. -/
theorem noS6A_Law3418 : ∀ v : Magma.tupS6A,
    ¬ @Equation3418 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3418) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3418) (by native_decide) v.1 v.2
    ((@Law3418.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3419 takes them (55 nodes). -/
def ordS6A_Law3419 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3419. -/
theorem noS6A_Law3419 : ∀ v : Magma.tupS6A,
    ¬ @Equation3419 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3419) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3419) (by native_decide) v.1 v.2
    ((@Law3419.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3420 takes them (26 nodes). -/
def ordS6A_Law3420 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3420. -/
theorem noS6A_Law3420 : ∀ v : Magma.tupS6A,
    ¬ @Equation3420 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3420) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3420) (by native_decide) v.1 v.2
    ((@Law3420.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3421 takes them (14 nodes). -/
def ordS6A_Law3421 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3421. -/
theorem noS6A_Law3421 : ∀ v : Magma.tupS6A,
    ¬ @Equation3421 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3421) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3421) (by native_decide) v.1 v.2
    ((@Law3421.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3422 takes them (55 nodes). -/
def ordS6A_Law3422 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3422. -/
theorem noS6A_Law3422 : ∀ v : Magma.tupS6A,
    ¬ @Equation3422 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3422) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3422) (by native_decide) v.1 v.2
    ((@Law3422.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3423 takes them (12 nodes). -/
def ordS6A_Law3423 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3423. -/
theorem noS6A_Law3423 : ∀ v : Magma.tupS6A,
    ¬ @Equation3423 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3423) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3423) (by native_decide) v.1 v.2
    ((@Law3423.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3424 takes them (12 nodes). -/
def ordS6A_Law3424 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3424. -/
theorem noS6A_Law3424 : ∀ v : Magma.tupS6A,
    ¬ @Equation3424 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3424) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3424) (by native_decide) v.1 v.2
    ((@Law3424.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3425 takes them (14 nodes). -/
def ordS6A_Law3425 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3425. -/
theorem noS6A_Law3425 : ∀ v : Magma.tupS6A,
    ¬ @Equation3425 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3425) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3425) (by native_decide) v.1 v.2
    ((@Law3425.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3426 takes them (55 nodes). -/
def ordS6A_Law3426 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3426. -/
theorem noS6A_Law3426 : ∀ v : Magma.tupS6A,
    ¬ @Equation3426 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3426) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3426) (by native_decide) v.1 v.2
    ((@Law3426.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3427 takes them (12 nodes). -/
def ordS6A_Law3427 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3427. -/
theorem noS6A_Law3427 : ∀ v : Magma.tupS6A,
    ¬ @Equation3427 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3427) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3427) (by native_decide) v.1 v.2
    ((@Law3427.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3428 takes them (12 nodes). -/
def ordS6A_Law3428 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3428. -/
theorem noS6A_Law3428 : ∀ v : Magma.tupS6A,
    ¬ @Equation3428 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3428) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3428) (by native_decide) v.1 v.2
    ((@Law3428.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3429 takes them (12 nodes). -/
def ordS6A_Law3429 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3429. -/
theorem noS6A_Law3429 : ∀ v : Magma.tupS6A,
    ¬ @Equation3429 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3429) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3429) (by native_decide) v.1 v.2
    ((@Law3429.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3430 takes them (25 nodes). -/
def ordS6A_Law3430 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3430. -/
theorem noS6A_Law3430 : ∀ v : Magma.tupS6A,
    ¬ @Equation3430 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3430) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3430) (by native_decide) v.1 v.2
    ((@Law3430.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3432 takes them (14 nodes). -/
def ordS6A_Law3432 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3432. -/
theorem noS6A_Law3432 : ∀ v : Magma.tupS6A,
    ¬ @Equation3432 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3432) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3432) (by native_decide) v.1 v.2
    ((@Law3432.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3433 takes them (14 nodes). -/
def ordS6A_Law3433 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3433. -/
theorem noS6A_Law3433 : ∀ v : Magma.tupS6A,
    ¬ @Equation3433 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3433) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3433) (by native_decide) v.1 v.2
    ((@Law3433.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3434 takes them (14 nodes). -/
def ordS6A_Law3434 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3434. -/
theorem noS6A_Law3434 : ∀ v : Magma.tupS6A,
    ¬ @Equation3434 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3434) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3434) (by native_decide) v.1 v.2
    ((@Law3434.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3435 takes them (61 nodes). -/
def ordS6A_Law3435 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3435. -/
theorem noS6A_Law3435 : ∀ v : Magma.tupS6A,
    ¬ @Equation3435 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3435) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3435) (by native_decide) v.1 v.2
    ((@Law3435.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3436 takes them (191 nodes). -/
def ordS6A_Law3436 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3436. -/
theorem noS6A_Law3436 : ∀ v : Magma.tupS6A,
    ¬ @Equation3436 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3436) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3436) (by native_decide) v.1 v.2
    ((@Law3436.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3437 takes them (55 nodes). -/
def ordS6A_Law3437 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3437. -/
theorem noS6A_Law3437 : ∀ v : Magma.tupS6A,
    ¬ @Equation3437 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3437) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3437) (by native_decide) v.1 v.2
    ((@Law3437.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3438 takes them (55 nodes). -/
def ordS6A_Law3438 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3438. -/
theorem noS6A_Law3438 : ∀ v : Magma.tupS6A,
    ¬ @Equation3438 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3438) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3438) (by native_decide) v.1 v.2
    ((@Law3438.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3439 takes them (26 nodes). -/
def ordS6A_Law3439 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3439. -/
theorem noS6A_Law3439 : ∀ v : Magma.tupS6A,
    ¬ @Equation3439 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3439) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3439) (by native_decide) v.1 v.2
    ((@Law3439.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3440 takes them (14 nodes). -/
def ordS6A_Law3440 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3440. -/
theorem noS6A_Law3440 : ∀ v : Magma.tupS6A,
    ¬ @Equation3440 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3440) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3440) (by native_decide) v.1 v.2
    ((@Law3440.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3441 takes them (55 nodes). -/
def ordS6A_Law3441 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3441. -/
theorem noS6A_Law3441 : ∀ v : Magma.tupS6A,
    ¬ @Equation3441 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3441) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3441) (by native_decide) v.1 v.2
    ((@Law3441.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3442 takes them (12 nodes). -/
def ordS6A_Law3442 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3442. -/
theorem noS6A_Law3442 : ∀ v : Magma.tupS6A,
    ¬ @Equation3442 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3442) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3442) (by native_decide) v.1 v.2
    ((@Law3442.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3443 takes them (12 nodes). -/
def ordS6A_Law3443 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3443. -/
theorem noS6A_Law3443 : ∀ v : Magma.tupS6A,
    ¬ @Equation3443 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3443) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3443) (by native_decide) v.1 v.2
    ((@Law3443.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3444 takes them (12 nodes). -/
def ordS6A_Law3444 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3444. -/
theorem noS6A_Law3444 : ∀ v : Magma.tupS6A,
    ¬ @Equation3444 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3444) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3444) (by native_decide) v.1 v.2
    ((@Law3444.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3445 takes them (14 nodes). -/
def ordS6A_Law3445 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3445. -/
theorem noS6A_Law3445 : ∀ v : Magma.tupS6A,
    ¬ @Equation3445 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3445) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3445) (by native_decide) v.1 v.2
    ((@Law3445.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3446 takes them (55 nodes). -/
def ordS6A_Law3446 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3446. -/
theorem noS6A_Law3446 : ∀ v : Magma.tupS6A,
    ¬ @Equation3446 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3446) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3446) (by native_decide) v.1 v.2
    ((@Law3446.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3447 takes them (12 nodes). -/
def ordS6A_Law3447 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3447. -/
theorem noS6A_Law3447 : ∀ v : Magma.tupS6A,
    ¬ @Equation3447 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3447) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3447) (by native_decide) v.1 v.2
    ((@Law3447.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3448 takes them (12 nodes). -/
def ordS6A_Law3448 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3448. -/
theorem noS6A_Law3448 : ∀ v : Magma.tupS6A,
    ¬ @Equation3448 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3448) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3448) (by native_decide) v.1 v.2
    ((@Law3448.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3449 takes them (12 nodes). -/
def ordS6A_Law3449 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3449. -/
theorem noS6A_Law3449 : ∀ v : Magma.tupS6A,
    ¬ @Equation3449 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3449) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3449) (by native_decide) v.1 v.2
    ((@Law3449.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3450 takes them (14 nodes). -/
def ordS6A_Law3450 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3450. -/
theorem noS6A_Law3450 : ∀ v : Magma.tupS6A,
    ¬ @Equation3450 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3450) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3450) (by native_decide) v.1 v.2
    ((@Law3450.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `45` equations. -/
theorem srch6A_refutes_33 :
    FamilyRefutes Magma.srch6A [
      3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3415, 3416, 3417, 3418, 3419,
      3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3432, 3433, 3434, 3435,
      3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450
    ] :=
  ⟨noS6A_Law3404, noS6A_Law3405, noS6A_Law3406, noS6A_Law3407, noS6A_Law3408, noS6A_Law3409, noS6A_Law3410, noS6A_Law3411, noS6A_Law3412, noS6A_Law3413, noS6A_Law3415, noS6A_Law3416, noS6A_Law3417, noS6A_Law3418, noS6A_Law3419, noS6A_Law3420, noS6A_Law3421, noS6A_Law3422, noS6A_Law3423, noS6A_Law3424, noS6A_Law3425, noS6A_Law3426, noS6A_Law3427, noS6A_Law3428, noS6A_Law3429, noS6A_Law3430, noS6A_Law3432, noS6A_Law3433, noS6A_Law3434, noS6A_Law3435, noS6A_Law3436, noS6A_Law3437, noS6A_Law3438, noS6A_Law3439, noS6A_Law3440, noS6A_Law3441, noS6A_Law3442, noS6A_Law3443, noS6A_Law3444, noS6A_Law3445, noS6A_Law3446, noS6A_Law3447, noS6A_Law3448, noS6A_Law3449, noS6A_Law3450⟩

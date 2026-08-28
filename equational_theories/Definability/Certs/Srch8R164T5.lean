import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 6 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `79` equations here, 797 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3431 takes them (10 nodes). -/
def ordS8R164_Law3431 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3431. -/
theorem noS8R164_Law3431 : ∀ v : Magma.tup8R164,
    ¬ @Equation3431 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3431) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3431) (by native_decide) v.1 v.2
    ((@Law3431.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3432 takes them (6 nodes). -/
def ordS8R164_Law3432 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3432. -/
theorem noS8R164_Law3432 : ∀ v : Magma.tup8R164,
    ¬ @Equation3432 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3432) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3432) (by native_decide) v.1 v.2
    ((@Law3432.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3433 takes them (6 nodes). -/
def ordS8R164_Law3433 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3433. -/
theorem noS8R164_Law3433 : ∀ v : Magma.tup8R164,
    ¬ @Equation3433 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3433) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3433) (by native_decide) v.1 v.2
    ((@Law3433.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3434 takes them (6 nodes). -/
def ordS8R164_Law3434 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3434. -/
theorem noS8R164_Law3434 : ∀ v : Magma.tup8R164,
    ¬ @Equation3434 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3434) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3434) (by native_decide) v.1 v.2
    ((@Law3434.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3435 takes them (7 nodes). -/
def ordS8R164_Law3435 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3435. -/
theorem noS8R164_Law3435 : ∀ v : Magma.tup8R164,
    ¬ @Equation3435 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3435) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3435) (by native_decide) v.1 v.2
    ((@Law3435.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3436 takes them (10 nodes). -/
def ordS8R164_Law3436 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3436. -/
theorem noS8R164_Law3436 : ∀ v : Magma.tup8R164,
    ¬ @Equation3436 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3436) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3436) (by native_decide) v.1 v.2
    ((@Law3436.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3437 takes them (7 nodes). -/
def ordS8R164_Law3437 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3437. -/
theorem noS8R164_Law3437 : ∀ v : Magma.tup8R164,
    ¬ @Equation3437 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3437) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3437) (by native_decide) v.1 v.2
    ((@Law3437.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3438 takes them (7 nodes). -/
def ordS8R164_Law3438 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3438. -/
theorem noS8R164_Law3438 : ∀ v : Magma.tup8R164,
    ¬ @Equation3438 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3438) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3438) (by native_decide) v.1 v.2
    ((@Law3438.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3439 takes them (6 nodes). -/
def ordS8R164_Law3439 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3439. -/
theorem noS8R164_Law3439 : ∀ v : Magma.tup8R164,
    ¬ @Equation3439 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3439) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3439) (by native_decide) v.1 v.2
    ((@Law3439.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3440 takes them (6 nodes). -/
def ordS8R164_Law3440 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3440. -/
theorem noS8R164_Law3440 : ∀ v : Magma.tup8R164,
    ¬ @Equation3440 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3440) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3440) (by native_decide) v.1 v.2
    ((@Law3440.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3441 takes them (10 nodes). -/
def ordS8R164_Law3441 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3441. -/
theorem noS8R164_Law3441 : ∀ v : Magma.tup8R164,
    ¬ @Equation3441 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3441) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3441) (by native_decide) v.1 v.2
    ((@Law3441.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3442 takes them (6 nodes). -/
def ordS8R164_Law3442 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3442. -/
theorem noS8R164_Law3442 : ∀ v : Magma.tup8R164,
    ¬ @Equation3442 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3442) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3442) (by native_decide) v.1 v.2
    ((@Law3442.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3443 takes them (6 nodes). -/
def ordS8R164_Law3443 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3443. -/
theorem noS8R164_Law3443 : ∀ v : Magma.tup8R164,
    ¬ @Equation3443 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3443) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3443) (by native_decide) v.1 v.2
    ((@Law3443.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3444 takes them (6 nodes). -/
def ordS8R164_Law3444 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3444. -/
theorem noS8R164_Law3444 : ∀ v : Magma.tup8R164,
    ¬ @Equation3444 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3444) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3444) (by native_decide) v.1 v.2
    ((@Law3444.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3445 takes them (6 nodes). -/
def ordS8R164_Law3445 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3445. -/
theorem noS8R164_Law3445 : ∀ v : Magma.tup8R164,
    ¬ @Equation3445 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3445) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3445) (by native_decide) v.1 v.2
    ((@Law3445.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3446 takes them (10 nodes). -/
def ordS8R164_Law3446 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3446. -/
theorem noS8R164_Law3446 : ∀ v : Magma.tup8R164,
    ¬ @Equation3446 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3446) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3446) (by native_decide) v.1 v.2
    ((@Law3446.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3447 takes them (6 nodes). -/
def ordS8R164_Law3447 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3447. -/
theorem noS8R164_Law3447 : ∀ v : Magma.tup8R164,
    ¬ @Equation3447 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3447) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3447) (by native_decide) v.1 v.2
    ((@Law3447.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3448 takes them (6 nodes). -/
def ordS8R164_Law3448 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3448. -/
theorem noS8R164_Law3448 : ∀ v : Magma.tup8R164,
    ¬ @Equation3448 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3448) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3448) (by native_decide) v.1 v.2
    ((@Law3448.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3449 takes them (6 nodes). -/
def ordS8R164_Law3449 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3449. -/
theorem noS8R164_Law3449 : ∀ v : Magma.tup8R164,
    ¬ @Equation3449 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3449) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3449) (by native_decide) v.1 v.2
    ((@Law3449.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3450 takes them (6 nodes). -/
def ordS8R164_Law3450 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3450. -/
theorem noS8R164_Law3450 : ∀ v : Magma.tup8R164,
    ¬ @Equation3450 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3450) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3450) (by native_decide) v.1 v.2
    ((@Law3450.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3451 takes them (10 nodes). -/
def ordS8R164_Law3451 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3451. -/
theorem noS8R164_Law3451 : ∀ v : Magma.tup8R164,
    ¬ @Equation3451 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3451) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3451) (by native_decide) v.1 v.2
    ((@Law3451.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3452 takes them (6 nodes). -/
def ordS8R164_Law3452 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3452. -/
theorem noS8R164_Law3452 : ∀ v : Magma.tup8R164,
    ¬ @Equation3452 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3452) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3452) (by native_decide) v.1 v.2
    ((@Law3452.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3453 takes them (6 nodes). -/
def ordS8R164_Law3453 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3453. -/
theorem noS8R164_Law3453 : ∀ v : Magma.tup8R164,
    ¬ @Equation3453 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3453) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3453) (by native_decide) v.1 v.2
    ((@Law3453.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3454 takes them (6 nodes). -/
def ordS8R164_Law3454 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3454. -/
theorem noS8R164_Law3454 : ∀ v : Magma.tup8R164,
    ¬ @Equation3454 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3454) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3454) (by native_decide) v.1 v.2
    ((@Law3454.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3455 takes them (6 nodes). -/
def ordS8R164_Law3455 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3455. -/
theorem noS8R164_Law3455 : ∀ v : Magma.tup8R164,
    ¬ @Equation3455 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3455) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law3455) (by native_decide) v.1 v.2
    ((@Law3455.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (23 nodes). -/
def ordS8R164_Law3458 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3458. -/
theorem noS8R164_Law3458 : ∀ v : Magma.tup8R164,
    ¬ @Equation3458 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3460 takes them (11 nodes). -/
def ordS8R164_Law3460 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3460. -/
theorem noS8R164_Law3460 : ∀ v : Magma.tup8R164,
    ¬ @Equation3460 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3460) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3460) (by native_decide) v.1 v.2
    ((@Law3460.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3461 takes them (21 nodes). -/
def ordS8R164_Law3461 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3461. -/
theorem noS8R164_Law3461 : ∀ v : Magma.tup8R164,
    ¬ @Equation3461 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3461) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3461) (by native_decide) v.1 v.2
    ((@Law3461.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3463 takes them (10 nodes). -/
def ordS8R164_Law3463 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3463. -/
theorem noS8R164_Law3463 : ∀ v : Magma.tup8R164,
    ¬ @Equation3463 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3463) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3463) (by native_decide) v.1 v.2
    ((@Law3463.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3467 takes them (20 nodes). -/
def ordS8R164_Law3467 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3467. -/
theorem noS8R164_Law3467 : ∀ v : Magma.tup8R164,
    ¬ @Equation3467 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3467) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3467) (by native_decide) v.1 v.2
    ((@Law3467.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3468 takes them (11 nodes). -/
def ordS8R164_Law3468 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3468. -/
theorem noS8R164_Law3468 : ∀ v : Magma.tup8R164,
    ¬ @Equation3468 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3469 takes them (12 nodes). -/
def ordS8R164_Law3469 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3469. -/
theorem noS8R164_Law3469 : ∀ v : Magma.tup8R164,
    ¬ @Equation3469 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3469) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3469) (by native_decide) v.1 v.2
    ((@Law3469.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3470 takes them (9 nodes). -/
def ordS8R164_Law3470 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3470. -/
theorem noS8R164_Law3470 : ∀ v : Magma.tup8R164,
    ¬ @Equation3470 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3470) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3470) (by native_decide) v.1 v.2
    ((@Law3470.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3475 takes them (13 nodes). -/
def ordS8R164_Law3475 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3475. -/
theorem noS8R164_Law3475 : ∀ v : Magma.tup8R164,
    ¬ @Equation3475 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3475) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3475) (by native_decide) v.1 v.2
    ((@Law3475.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3476 takes them (6 nodes). -/
def ordS8R164_Law3476 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3476. -/
theorem noS8R164_Law3476 : ∀ v : Magma.tup8R164,
    ¬ @Equation3476 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3476) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3476) (by native_decide) v.1 v.2
    ((@Law3476.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3477 takes them (11 nodes). -/
def ordS8R164_Law3477 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3477. -/
theorem noS8R164_Law3477 : ∀ v : Magma.tup8R164,
    ¬ @Equation3477 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3477) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3477) (by native_decide) v.1 v.2
    ((@Law3477.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3478 takes them (12 nodes). -/
def ordS8R164_Law3478 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3478. -/
theorem noS8R164_Law3478 : ∀ v : Magma.tup8R164,
    ¬ @Equation3478 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3478) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3478) (by native_decide) v.1 v.2
    ((@Law3478.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3479 takes them (9 nodes). -/
def ordS8R164_Law3479 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3479. -/
theorem noS8R164_Law3479 : ∀ v : Magma.tup8R164,
    ¬ @Equation3479 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3479) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3479) (by native_decide) v.1 v.2
    ((@Law3479.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3480 takes them (6 nodes). -/
def ordS8R164_Law3480 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3480. -/
theorem noS8R164_Law3480 : ∀ v : Magma.tup8R164,
    ¬ @Equation3480 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3480) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3480) (by native_decide) v.1 v.2
    ((@Law3480.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3482 takes them (16 nodes). -/
def ordS8R164_Law3482 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3482. -/
theorem noS8R164_Law3482 : ∀ v : Magma.tup8R164,
    ¬ @Equation3482 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3482) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3482) (by native_decide) v.1 v.2
    ((@Law3482.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3483 takes them (8 nodes). -/
def ordS8R164_Law3483 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3483. -/
theorem noS8R164_Law3483 : ∀ v : Magma.tup8R164,
    ¬ @Equation3483 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3483) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3483) (by native_decide) v.1 v.2
    ((@Law3483.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3487 takes them (12 nodes). -/
def ordS8R164_Law3487 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3487. -/
theorem noS8R164_Law3487 : ∀ v : Magma.tup8R164,
    ¬ @Equation3487 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3487) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3487) (by native_decide) v.1 v.2
    ((@Law3487.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3488 takes them (15 nodes). -/
def ordS8R164_Law3488 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3488. -/
theorem noS8R164_Law3488 : ∀ v : Magma.tup8R164,
    ¬ @Equation3488 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3488) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3488) (by native_decide) v.1 v.2
    ((@Law3488.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3490 takes them (8 nodes). -/
def ordS8R164_Law3490 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3490. -/
theorem noS8R164_Law3490 : ∀ v : Magma.tup8R164,
    ¬ @Equation3490 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3490) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3490) (by native_decide) v.1 v.2
    ((@Law3490.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3491 takes them (11 nodes). -/
def ordS8R164_Law3491 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3491. -/
theorem noS8R164_Law3491 : ∀ v : Magma.tup8R164,
    ¬ @Equation3491 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3491) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3491) (by native_decide) v.1 v.2
    ((@Law3491.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3492 takes them (12 nodes). -/
def ordS8R164_Law3492 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3492. -/
theorem noS8R164_Law3492 : ∀ v : Magma.tup8R164,
    ¬ @Equation3492 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3492) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3492) (by native_decide) v.1 v.2
    ((@Law3492.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3493 takes them (8 nodes). -/
def ordS8R164_Law3493 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3493. -/
theorem noS8R164_Law3493 : ∀ v : Magma.tup8R164,
    ¬ @Equation3493 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3493) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3493) (by native_decide) v.1 v.2
    ((@Law3493.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3494 takes them (6 nodes). -/
def ordS8R164_Law3494 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3494. -/
theorem noS8R164_Law3494 : ∀ v : Magma.tup8R164,
    ¬ @Equation3494 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3494) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3494) (by native_decide) v.1 v.2
    ((@Law3494.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3495 takes them (10 nodes). -/
def ordS8R164_Law3495 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3495. -/
theorem noS8R164_Law3495 : ∀ v : Magma.tup8R164,
    ¬ @Equation3495 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3495) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3495) (by native_decide) v.1 v.2
    ((@Law3495.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3496 takes them (12 nodes). -/
def ordS8R164_Law3496 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3496. -/
theorem noS8R164_Law3496 : ∀ v : Magma.tup8R164,
    ¬ @Equation3496 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3496) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3496) (by native_decide) v.1 v.2
    ((@Law3496.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3498 takes them (6 nodes). -/
def ordS8R164_Law3498 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3498. -/
theorem noS8R164_Law3498 : ∀ v : Magma.tup8R164,
    ¬ @Equation3498 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3498) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3498) (by native_decide) v.1 v.2
    ((@Law3498.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3503 takes them (10 nodes). -/
def ordS8R164_Law3503 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3503. -/
theorem noS8R164_Law3503 : ∀ v : Magma.tup8R164,
    ¬ @Equation3503 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3503) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3503) (by native_decide) v.1 v.2
    ((@Law3503.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3504 takes them (12 nodes). -/
def ordS8R164_Law3504 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3504. -/
theorem noS8R164_Law3504 : ∀ v : Magma.tup8R164,
    ¬ @Equation3504 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3504) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3504) (by native_decide) v.1 v.2
    ((@Law3504.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3505 takes them (8 nodes). -/
def ordS8R164_Law3505 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3505. -/
theorem noS8R164_Law3505 : ∀ v : Magma.tup8R164,
    ¬ @Equation3505 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3505) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3505) (by native_decide) v.1 v.2
    ((@Law3505.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3506 takes them (9 nodes). -/
def ordS8R164_Law3506 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3506. -/
theorem noS8R164_Law3506 : ∀ v : Magma.tup8R164,
    ¬ @Equation3506 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3506) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3506) (by native_decide) v.1 v.2
    ((@Law3506.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3507 takes them (6 nodes). -/
def ordS8R164_Law3507 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3507. -/
theorem noS8R164_Law3507 : ∀ v : Magma.tup8R164,
    ¬ @Equation3507 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3507) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3507) (by native_decide) v.1 v.2
    ((@Law3507.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3508 takes them (9 nodes). -/
def ordS8R164_Law3508 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3508. -/
theorem noS8R164_Law3508 : ∀ v : Magma.tup8R164,
    ¬ @Equation3508 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3508) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3508) (by native_decide) v.1 v.2
    ((@Law3508.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3510 takes them (9 nodes). -/
def ordS8R164_Law3510 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3510. -/
theorem noS8R164_Law3510 : ∀ v : Magma.tup8R164,
    ¬ @Equation3510 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3510) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3510) (by native_decide) v.1 v.2
    ((@Law3510.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3512 takes them (25 nodes). -/
def ordS8R164_Law3512 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3512. -/
theorem noS8R164_Law3512 : ∀ v : Magma.tup8R164,
    ¬ @Equation3512 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3512) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3512) (by native_decide) v.1 v.2
    ((@Law3512.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3513 takes them (9 nodes). -/
def ordS8R164_Law3513 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3513. -/
theorem noS8R164_Law3513 : ∀ v : Magma.tup8R164,
    ¬ @Equation3513 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3513) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3513) (by native_decide) v.1 v.2
    ((@Law3513.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3514 takes them (9 nodes). -/
def ordS8R164_Law3514 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3514. -/
theorem noS8R164_Law3514 : ∀ v : Magma.tup8R164,
    ¬ @Equation3514 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3514) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3514) (by native_decide) v.1 v.2
    ((@Law3514.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3515 takes them (13 nodes). -/
def ordS8R164_Law3515 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3515. -/
theorem noS8R164_Law3515 : ∀ v : Magma.tup8R164,
    ¬ @Equation3515 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3515) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3515) (by native_decide) v.1 v.2
    ((@Law3515.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3516 takes them (9 nodes). -/
def ordS8R164_Law3516 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3516. -/
theorem noS8R164_Law3516 : ∀ v : Magma.tup8R164,
    ¬ @Equation3516 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3516) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3516) (by native_decide) v.1 v.2
    ((@Law3516.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3517 takes them (9 nodes). -/
def ordS8R164_Law3517 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3517. -/
theorem noS8R164_Law3517 : ∀ v : Magma.tup8R164,
    ¬ @Equation3517 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3517) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3517) (by native_decide) v.1 v.2
    ((@Law3517.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3519 takes them (29 nodes). -/
def ordS8R164_Law3519 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3519. -/
theorem noS8R164_Law3519 : ∀ v : Magma.tup8R164,
    ¬ @Equation3519 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3519) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3519) (by native_decide) v.1 v.2
    ((@Law3519.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (9 nodes). -/
def ordS8R164_Law3520 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3520. -/
theorem noS8R164_Law3520 : ∀ v : Magma.tup8R164,
    ¬ @Equation3520 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (17 nodes). -/
def ordS8R164_Law3521 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3521. -/
theorem noS8R164_Law3521 : ∀ v : Magma.tup8R164,
    ¬ @Equation3521 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (9 nodes). -/
def ordS8R164_Law3523 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3523. -/
theorem noS8R164_Law3523 : ∀ v : Magma.tup8R164,
    ¬ @Equation3523 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (10 nodes). -/
def ordS8R164_Law3524 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3524. -/
theorem noS8R164_Law3524 : ∀ v : Magma.tup8R164,
    ¬ @Equation3524 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3525 takes them (19 nodes). -/
def ordS8R164_Law3525 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3525. -/
theorem noS8R164_Law3525 : ∀ v : Magma.tup8R164,
    ¬ @Equation3525 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3525) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3525) (by native_decide) v.1 v.2
    ((@Law3525.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (9 nodes). -/
def ordS8R164_Law3527 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3527. -/
theorem noS8R164_Law3527 : ∀ v : Magma.tup8R164,
    ¬ @Equation3527 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3528 takes them (9 nodes). -/
def ordS8R164_Law3528 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3528. -/
theorem noS8R164_Law3528 : ∀ v : Magma.tup8R164,
    ¬ @Equation3528 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3528) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3528) (by native_decide) v.1 v.2
    ((@Law3528.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (18 nodes). -/
def ordS8R164_Law3529 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3529. -/
theorem noS8R164_Law3529 : ∀ v : Magma.tup8R164,
    ¬ @Equation3529 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3530 takes them (9 nodes). -/
def ordS8R164_Law3530 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3530. -/
theorem noS8R164_Law3530 : ∀ v : Magma.tup8R164,
    ¬ @Equation3530 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3530) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3530) (by native_decide) v.1 v.2
    ((@Law3530.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3531 takes them (9 nodes). -/
def ordS8R164_Law3531 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3531. -/
theorem noS8R164_Law3531 : ∀ v : Magma.tup8R164,
    ¬ @Equation3531 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3531) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3531) (by native_decide) v.1 v.2
    ((@Law3531.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3532 takes them (10 nodes). -/
def ordS8R164_Law3532 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3532. -/
theorem noS8R164_Law3532 : ∀ v : Magma.tup8R164,
    ¬ @Equation3532 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3532) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3532) (by native_decide) v.1 v.2
    ((@Law3532.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3533 takes them (14 nodes). -/
def ordS8R164_Law3533 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3533. -/
theorem noS8R164_Law3533 : ∀ v : Magma.tup8R164,
    ¬ @Equation3533 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3533) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3533) (by native_decide) v.1 v.2
    ((@Law3533.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3535 takes them (9 nodes). -/
def ordS8R164_Law3535 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3535. -/
theorem noS8R164_Law3535 : ∀ v : Magma.tup8R164,
    ¬ @Equation3535 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3535) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3535) (by native_decide) v.1 v.2
    ((@Law3535.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3536 takes them (9 nodes). -/
def ordS8R164_Law3536 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3536. -/
theorem noS8R164_Law3536 : ∀ v : Magma.tup8R164,
    ¬ @Equation3536 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3536) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3536) (by native_decide) v.1 v.2
    ((@Law3536.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `79` equations. -/
theorem srch8R164_refutes_5 :
    FamilyRefutes Magma.srch8R164 [
      3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445,
      3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3458, 3460, 3461, 3463, 3467,
      3468, 3469, 3470, 3475, 3476, 3477, 3478, 3479, 3480, 3482, 3483, 3487, 3488, 3490, 3491,
      3492, 3493, 3494, 3495, 3496, 3498, 3503, 3504, 3505, 3506, 3507, 3508, 3510, 3512, 3513,
      3514, 3515, 3516, 3517, 3519, 3520, 3521, 3523, 3524, 3525, 3527, 3528, 3529, 3530, 3531,
      3532, 3533, 3535, 3536
    ] :=
  ⟨noS8R164_Law3431, noS8R164_Law3432, noS8R164_Law3433, noS8R164_Law3434, noS8R164_Law3435, noS8R164_Law3436, noS8R164_Law3437, noS8R164_Law3438, noS8R164_Law3439, noS8R164_Law3440, noS8R164_Law3441, noS8R164_Law3442, noS8R164_Law3443, noS8R164_Law3444, noS8R164_Law3445, noS8R164_Law3446, noS8R164_Law3447, noS8R164_Law3448, noS8R164_Law3449, noS8R164_Law3450, noS8R164_Law3451, noS8R164_Law3452, noS8R164_Law3453, noS8R164_Law3454, noS8R164_Law3455, noS8R164_Law3458, noS8R164_Law3460, noS8R164_Law3461, noS8R164_Law3463, noS8R164_Law3467, noS8R164_Law3468, noS8R164_Law3469, noS8R164_Law3470, noS8R164_Law3475, noS8R164_Law3476, noS8R164_Law3477, noS8R164_Law3478, noS8R164_Law3479, noS8R164_Law3480, noS8R164_Law3482, noS8R164_Law3483, noS8R164_Law3487, noS8R164_Law3488, noS8R164_Law3490, noS8R164_Law3491, noS8R164_Law3492, noS8R164_Law3493, noS8R164_Law3494, noS8R164_Law3495, noS8R164_Law3496, noS8R164_Law3498, noS8R164_Law3503, noS8R164_Law3504, noS8R164_Law3505, noS8R164_Law3506, noS8R164_Law3507, noS8R164_Law3508, noS8R164_Law3510, noS8R164_Law3512, noS8R164_Law3513, noS8R164_Law3514, noS8R164_Law3515, noS8R164_Law3516, noS8R164_Law3517, noS8R164_Law3519, noS8R164_Law3520, noS8R164_Law3521, noS8R164_Law3523, noS8R164_Law3524, noS8R164_Law3525, noS8R164_Law3527, noS8R164_Law3528, noS8R164_Law3529, noS8R164_Law3530, noS8R164_Law3531, noS8R164_Law3532, noS8R164_Law3533, noS8R164_Law3535, noS8R164_Law3536⟩

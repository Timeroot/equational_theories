import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 16 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `83` equations here, 678 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4472 takes them (18 nodes). -/
def ordS8R164_Law4472 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4472. -/
theorem noS8R164_Law4472 : ∀ v : Magma.tup8R164,
    ¬ @Equation4472 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4474 takes them (9 nodes). -/
def ordS8R164_Law4474 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4474. -/
theorem noS8R164_Law4474 : ∀ v : Magma.tup8R164,
    ¬ @Equation4474 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4474) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4474) (by native_decide) v.1 v.2
    ((@Law4474.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4475 takes them (11 nodes). -/
def ordS8R164_Law4475 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4475. -/
theorem noS8R164_Law4475 : ∀ v : Magma.tup8R164,
    ¬ @Equation4475 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4475) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4475) (by native_decide) v.1 v.2
    ((@Law4475.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4476 takes them (13 nodes). -/
def ordS8R164_Law4476 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4476. -/
theorem noS8R164_Law4476 : ∀ v : Magma.tup8R164,
    ¬ @Equation4476 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4476) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4476) (by native_decide) v.1 v.2
    ((@Law4476.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4478 takes them (9 nodes). -/
def ordS8R164_Law4478 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4478. -/
theorem noS8R164_Law4478 : ∀ v : Magma.tup8R164,
    ¬ @Equation4478 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4478) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4478) (by native_decide) v.1 v.2
    ((@Law4478.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4479 takes them (13 nodes). -/
def ordS8R164_Law4479 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4479. -/
theorem noS8R164_Law4479 : ∀ v : Magma.tup8R164,
    ¬ @Equation4479 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4479) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4479) (by native_decide) v.1 v.2
    ((@Law4479.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4481 takes them (6 nodes). -/
def ordS8R164_Law4481 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4481. -/
theorem noS8R164_Law4481 : ∀ v : Magma.tup8R164,
    ¬ @Equation4481 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4481) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4481) (by native_decide) v.1 v.2
    ((@Law4481.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4485 takes them (7 nodes). -/
def ordS8R164_Law4485 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4485. -/
theorem noS8R164_Law4485 : ∀ v : Magma.tup8R164,
    ¬ @Equation4485 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4485) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4485) (by native_decide) v.1 v.2
    ((@Law4485.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4486 takes them (11 nodes). -/
def ordS8R164_Law4486 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4486. -/
theorem noS8R164_Law4486 : ∀ v : Magma.tup8R164,
    ¬ @Equation4486 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4486) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4486) (by native_decide) v.1 v.2
    ((@Law4486.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4487 takes them (9 nodes). -/
def ordS8R164_Law4487 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4487. -/
theorem noS8R164_Law4487 : ∀ v : Magma.tup8R164,
    ¬ @Equation4487 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4487) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4487) (by native_decide) v.1 v.2
    ((@Law4487.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4488 takes them (6 nodes). -/
def ordS8R164_Law4488 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4488. -/
theorem noS8R164_Law4488 : ∀ v : Magma.tup8R164,
    ¬ @Equation4488 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4488) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4488) (by native_decide) v.1 v.2
    ((@Law4488.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4489 takes them (9 nodes). -/
def ordS8R164_Law4489 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4489. -/
theorem noS8R164_Law4489 : ∀ v : Magma.tup8R164,
    ¬ @Equation4489 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4489) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4489) (by native_decide) v.1 v.2
    ((@Law4489.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4490 takes them (10 nodes). -/
def ordS8R164_Law4490 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4490. -/
theorem noS8R164_Law4490 : ∀ v : Magma.tup8R164,
    ¬ @Equation4490 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4490) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4490) (by native_decide) v.1 v.2
    ((@Law4490.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4492 takes them (6 nodes). -/
def ordS8R164_Law4492 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4492. -/
theorem noS8R164_Law4492 : ∀ v : Magma.tup8R164,
    ¬ @Equation4492 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4492) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4492) (by native_decide) v.1 v.2
    ((@Law4492.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4493 takes them (7 nodes). -/
def ordS8R164_Law4493 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4493. -/
theorem noS8R164_Law4493 : ∀ v : Magma.tup8R164,
    ¬ @Equation4493 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4493) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4493) (by native_decide) v.1 v.2
    ((@Law4493.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4494 takes them (11 nodes). -/
def ordS8R164_Law4494 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4494. -/
theorem noS8R164_Law4494 : ∀ v : Magma.tup8R164,
    ¬ @Equation4494 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4494) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4494) (by native_decide) v.1 v.2
    ((@Law4494.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4495 takes them (8 nodes). -/
def ordS8R164_Law4495 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4495. -/
theorem noS8R164_Law4495 : ∀ v : Magma.tup8R164,
    ¬ @Equation4495 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4495) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4495) (by native_decide) v.1 v.2
    ((@Law4495.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4496 takes them (6 nodes). -/
def ordS8R164_Law4496 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4496. -/
theorem noS8R164_Law4496 : ∀ v : Magma.tup8R164,
    ¬ @Equation4496 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4496) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4496) (by native_decide) v.1 v.2
    ((@Law4496.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4501 takes them (7 nodes). -/
def ordS8R164_Law4501 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4501. -/
theorem noS8R164_Law4501 : ∀ v : Magma.tup8R164,
    ¬ @Equation4501 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4501) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4501) (by native_decide) v.1 v.2
    ((@Law4501.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4502 takes them (10 nodes). -/
def ordS8R164_Law4502 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4502. -/
theorem noS8R164_Law4502 : ∀ v : Magma.tup8R164,
    ¬ @Equation4502 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4502) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4502) (by native_decide) v.1 v.2
    ((@Law4502.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4503 takes them (8 nodes). -/
def ordS8R164_Law4503 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4503. -/
theorem noS8R164_Law4503 : ∀ v : Magma.tup8R164,
    ¬ @Equation4503 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4503) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4503) (by native_decide) v.1 v.2
    ((@Law4503.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4504 takes them (9 nodes). -/
def ordS8R164_Law4504 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4504. -/
theorem noS8R164_Law4504 : ∀ v : Magma.tup8R164,
    ¬ @Equation4504 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4504) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4504) (by native_decide) v.1 v.2
    ((@Law4504.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4505 takes them (6 nodes). -/
def ordS8R164_Law4505 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4505. -/
theorem noS8R164_Law4505 : ∀ v : Magma.tup8R164,
    ¬ @Equation4505 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4505) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4505) (by native_decide) v.1 v.2
    ((@Law4505.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4506 takes them (9 nodes). -/
def ordS8R164_Law4506 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4506. -/
theorem noS8R164_Law4506 : ∀ v : Magma.tup8R164,
    ¬ @Equation4506 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4506) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4506) (by native_decide) v.1 v.2
    ((@Law4506.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4507 takes them (9 nodes). -/
def ordS8R164_Law4507 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4507. -/
theorem noS8R164_Law4507 : ∀ v : Magma.tup8R164,
    ¬ @Equation4507 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4507) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4507) (by native_decide) v.1 v.2
    ((@Law4507.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4508 takes them (13 nodes). -/
def ordS8R164_Law4508 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4508. -/
theorem noS8R164_Law4508 : ∀ v : Magma.tup8R164,
    ¬ @Equation4508 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4508) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4508) (by native_decide) v.1 v.2
    ((@Law4508.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4509 takes them (9 nodes). -/
def ordS8R164_Law4509 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4509. -/
theorem noS8R164_Law4509 : ∀ v : Magma.tup8R164,
    ¬ @Equation4509 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4509) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4509) (by native_decide) v.1 v.2
    ((@Law4509.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4510 takes them (9 nodes). -/
def ordS8R164_Law4510 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4510. -/
theorem noS8R164_Law4510 : ∀ v : Magma.tup8R164,
    ¬ @Equation4510 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4510) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4510) (by native_decide) v.1 v.2
    ((@Law4510.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4511 takes them (9 nodes). -/
def ordS8R164_Law4511 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4511. -/
theorem noS8R164_Law4511 : ∀ v : Magma.tup8R164,
    ¬ @Equation4511 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4511) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4511) (by native_decide) v.1 v.2
    ((@Law4511.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4513 takes them (9 nodes). -/
def ordS8R164_Law4513 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4513. -/
theorem noS8R164_Law4513 : ∀ v : Magma.tup8R164,
    ¬ @Equation4513 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4513) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4513) (by native_decide) v.1 v.2
    ((@Law4513.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4514 takes them (10 nodes). -/
def ordS8R164_Law4514 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4514. -/
theorem noS8R164_Law4514 : ∀ v : Magma.tup8R164,
    ¬ @Equation4514 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4514) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4514) (by native_decide) v.1 v.2
    ((@Law4514.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4516 takes them (13 nodes). -/
def ordS8R164_Law4516 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4516. -/
theorem noS8R164_Law4516 : ∀ v : Magma.tup8R164,
    ¬ @Equation4516 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4516) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4516) (by native_decide) v.1 v.2
    ((@Law4516.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4517 takes them (9 nodes). -/
def ordS8R164_Law4517 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4517. -/
theorem noS8R164_Law4517 : ∀ v : Magma.tup8R164,
    ¬ @Equation4517 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4517) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4517) (by native_decide) v.1 v.2
    ((@Law4517.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4518 takes them (9 nodes). -/
def ordS8R164_Law4518 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4518. -/
theorem noS8R164_Law4518 : ∀ v : Magma.tup8R164,
    ¬ @Equation4518 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4518) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4518) (by native_decide) v.1 v.2
    ((@Law4518.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4519 takes them (9 nodes). -/
def ordS8R164_Law4519 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4519. -/
theorem noS8R164_Law4519 : ∀ v : Magma.tup8R164,
    ¬ @Equation4519 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4519) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4519) (by native_decide) v.1 v.2
    ((@Law4519.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4520 takes them (13 nodes). -/
def ordS8R164_Law4520 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4520. -/
theorem noS8R164_Law4520 : ∀ v : Magma.tup8R164,
    ¬ @Equation4520 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4520) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4520) (by native_decide) v.1 v.2
    ((@Law4520.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4521 takes them (9 nodes). -/
def ordS8R164_Law4521 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4521. -/
theorem noS8R164_Law4521 : ∀ v : Magma.tup8R164,
    ¬ @Equation4521 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4521) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4521) (by native_decide) v.1 v.2
    ((@Law4521.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4522 takes them (9 nodes). -/
def ordS8R164_Law4522 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4522. -/
theorem noS8R164_Law4522 : ∀ v : Magma.tup8R164,
    ¬ @Equation4522 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4522) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4522) (by native_decide) v.1 v.2
    ((@Law4522.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4523 takes them (6 nodes). -/
def ordS8R164_Law4523 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4523. -/
theorem noS8R164_Law4523 : ∀ v : Magma.tup8R164,
    ¬ @Equation4523 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4523) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4523) (by native_decide) v.1 v.2
    ((@Law4523.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4524 takes them (6 nodes). -/
def ordS8R164_Law4524 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4524. -/
theorem noS8R164_Law4524 : ∀ v : Magma.tup8R164,
    ¬ @Equation4524 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4524) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4524) (by native_decide) v.1 v.2
    ((@Law4524.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4526 takes them (6 nodes). -/
def ordS8R164_Law4526 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4526. -/
theorem noS8R164_Law4526 : ∀ v : Magma.tup8R164,
    ¬ @Equation4526 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4526) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4526) (by native_decide) v.1 v.2
    ((@Law4526.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4527 takes them (6 nodes). -/
def ordS8R164_Law4527 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4527. -/
theorem noS8R164_Law4527 : ∀ v : Magma.tup8R164,
    ¬ @Equation4527 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4527) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4527) (by native_decide) v.1 v.2
    ((@Law4527.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4528 takes them (6 nodes). -/
def ordS8R164_Law4528 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4528. -/
theorem noS8R164_Law4528 : ∀ v : Magma.tup8R164,
    ¬ @Equation4528 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4528) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4528) (by native_decide) v.1 v.2
    ((@Law4528.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4529 takes them (10 nodes). -/
def ordS8R164_Law4529 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4529. -/
theorem noS8R164_Law4529 : ∀ v : Magma.tup8R164,
    ¬ @Equation4529 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4529) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4529) (by native_decide) v.1 v.2
    ((@Law4529.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4530 takes them (6 nodes). -/
def ordS8R164_Law4530 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4530. -/
theorem noS8R164_Law4530 : ∀ v : Magma.tup8R164,
    ¬ @Equation4530 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4530) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4530) (by native_decide) v.1 v.2
    ((@Law4530.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4532 takes them (7 nodes). -/
def ordS8R164_Law4532 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4532. -/
theorem noS8R164_Law4532 : ∀ v : Magma.tup8R164,
    ¬ @Equation4532 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4532) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4532) (by native_decide) v.1 v.2
    ((@Law4532.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4533 takes them (10 nodes). -/
def ordS8R164_Law4533 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4533. -/
theorem noS8R164_Law4533 : ∀ v : Magma.tup8R164,
    ¬ @Equation4533 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4533) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4533) (by native_decide) v.1 v.2
    ((@Law4533.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4534 takes them (6 nodes). -/
def ordS8R164_Law4534 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4534. -/
theorem noS8R164_Law4534 : ∀ v : Magma.tup8R164,
    ¬ @Equation4534 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4534) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4534) (by native_decide) v.1 v.2
    ((@Law4534.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4535 takes them (6 nodes). -/
def ordS8R164_Law4535 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4535. -/
theorem noS8R164_Law4535 : ∀ v : Magma.tup8R164,
    ¬ @Equation4535 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4535) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4535) (by native_decide) v.1 v.2
    ((@Law4535.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4536 takes them (6 nodes). -/
def ordS8R164_Law4536 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4536. -/
theorem noS8R164_Law4536 : ∀ v : Magma.tup8R164,
    ¬ @Equation4536 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4536) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4536) (by native_decide) v.1 v.2
    ((@Law4536.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4537 takes them (10 nodes). -/
def ordS8R164_Law4537 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4537. -/
theorem noS8R164_Law4537 : ∀ v : Magma.tup8R164,
    ¬ @Equation4537 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4537) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4537) (by native_decide) v.1 v.2
    ((@Law4537.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4538 takes them (6 nodes). -/
def ordS8R164_Law4538 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4538. -/
theorem noS8R164_Law4538 : ∀ v : Magma.tup8R164,
    ¬ @Equation4538 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4538) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4538) (by native_decide) v.1 v.2
    ((@Law4538.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4539 takes them (6 nodes). -/
def ordS8R164_Law4539 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4539. -/
theorem noS8R164_Law4539 : ∀ v : Magma.tup8R164,
    ¬ @Equation4539 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4539) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4539) (by native_decide) v.1 v.2
    ((@Law4539.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4540 takes them (7 nodes). -/
def ordS8R164_Law4540 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4540. -/
theorem noS8R164_Law4540 : ∀ v : Magma.tup8R164,
    ¬ @Equation4540 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4540) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4540) (by native_decide) v.1 v.2
    ((@Law4540.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4542 takes them (10 nodes). -/
def ordS8R164_Law4542 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4542. -/
theorem noS8R164_Law4542 : ∀ v : Magma.tup8R164,
    ¬ @Equation4542 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4542) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4542) (by native_decide) v.1 v.2
    ((@Law4542.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4543 takes them (6 nodes). -/
def ordS8R164_Law4543 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4543. -/
theorem noS8R164_Law4543 : ∀ v : Magma.tup8R164,
    ¬ @Equation4543 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4543) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4543) (by native_decide) v.1 v.2
    ((@Law4543.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4545 takes them (7 nodes). -/
def ordS8R164_Law4545 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4545. -/
theorem noS8R164_Law4545 : ∀ v : Magma.tup8R164,
    ¬ @Equation4545 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4545) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4545) (by native_decide) v.1 v.2
    ((@Law4545.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4546 takes them (10 nodes). -/
def ordS8R164_Law4546 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4546. -/
theorem noS8R164_Law4546 : ∀ v : Magma.tup8R164,
    ¬ @Equation4546 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4546) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4546) (by native_decide) v.1 v.2
    ((@Law4546.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4547 takes them (6 nodes). -/
def ordS8R164_Law4547 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4547. -/
theorem noS8R164_Law4547 : ∀ v : Magma.tup8R164,
    ¬ @Equation4547 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4547) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4547) (by native_decide) v.1 v.2
    ((@Law4547.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4548 takes them (7 nodes). -/
def ordS8R164_Law4548 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4548. -/
theorem noS8R164_Law4548 : ∀ v : Magma.tup8R164,
    ¬ @Equation4548 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4548) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4548) (by native_decide) v.1 v.2
    ((@Law4548.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4549 takes them (7 nodes). -/
def ordS8R164_Law4549 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4549. -/
theorem noS8R164_Law4549 : ∀ v : Magma.tup8R164,
    ¬ @Equation4549 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4549) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4549) (by native_decide) v.1 v.2
    ((@Law4549.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4550 takes them (10 nodes). -/
def ordS8R164_Law4550 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4550. -/
theorem noS8R164_Law4550 : ∀ v : Magma.tup8R164,
    ¬ @Equation4550 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4550) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4550) (by native_decide) v.1 v.2
    ((@Law4550.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4551 takes them (6 nodes). -/
def ordS8R164_Law4551 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4551. -/
theorem noS8R164_Law4551 : ∀ v : Magma.tup8R164,
    ¬ @Equation4551 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4551) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4551) (by native_decide) v.1 v.2
    ((@Law4551.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4552 takes them (7 nodes). -/
def ordS8R164_Law4552 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4552. -/
theorem noS8R164_Law4552 : ∀ v : Magma.tup8R164,
    ¬ @Equation4552 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4552) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4552) (by native_decide) v.1 v.2
    ((@Law4552.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4553 takes them (7 nodes). -/
def ordS8R164_Law4553 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4553. -/
theorem noS8R164_Law4553 : ∀ v : Magma.tup8R164,
    ¬ @Equation4553 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4553) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4553) (by native_decide) v.1 v.2
    ((@Law4553.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4554 takes them (10 nodes). -/
def ordS8R164_Law4554 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4554. -/
theorem noS8R164_Law4554 : ∀ v : Magma.tup8R164,
    ¬ @Equation4554 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4554) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4554) (by native_decide) v.1 v.2
    ((@Law4554.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4555 takes them (7 nodes). -/
def ordS8R164_Law4555 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4555. -/
theorem noS8R164_Law4555 : ∀ v : Magma.tup8R164,
    ¬ @Equation4555 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4555) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4555) (by native_decide) v.1 v.2
    ((@Law4555.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4556 takes them (6 nodes). -/
def ordS8R164_Law4556 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4556. -/
theorem noS8R164_Law4556 : ∀ v : Magma.tup8R164,
    ¬ @Equation4556 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4556) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4556) (by native_decide) v.1 v.2
    ((@Law4556.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4557 takes them (6 nodes). -/
def ordS8R164_Law4557 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4557. -/
theorem noS8R164_Law4557 : ∀ v : Magma.tup8R164,
    ¬ @Equation4557 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4557) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4557) (by native_decide) v.1 v.2
    ((@Law4557.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4558 takes them (6 nodes). -/
def ordS8R164_Law4558 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4558. -/
theorem noS8R164_Law4558 : ∀ v : Magma.tup8R164,
    ¬ @Equation4558 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4558) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4558) (by native_decide) v.1 v.2
    ((@Law4558.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4559 takes them (10 nodes). -/
def ordS8R164_Law4559 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4559. -/
theorem noS8R164_Law4559 : ∀ v : Magma.tup8R164,
    ¬ @Equation4559 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4559) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4559) (by native_decide) v.1 v.2
    ((@Law4559.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4560 takes them (6 nodes). -/
def ordS8R164_Law4560 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4560. -/
theorem noS8R164_Law4560 : ∀ v : Magma.tup8R164,
    ¬ @Equation4560 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4560) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4560) (by native_decide) v.1 v.2
    ((@Law4560.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4561 takes them (6 nodes). -/
def ordS8R164_Law4561 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4561. -/
theorem noS8R164_Law4561 : ∀ v : Magma.tup8R164,
    ¬ @Equation4561 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4561) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4561) (by native_decide) v.1 v.2
    ((@Law4561.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4562 takes them (6 nodes). -/
def ordS8R164_Law4562 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4562. -/
theorem noS8R164_Law4562 : ∀ v : Magma.tup8R164,
    ¬ @Equation4562 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4562) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4562) (by native_decide) v.1 v.2
    ((@Law4562.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4563 takes them (6 nodes). -/
def ordS8R164_Law4563 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4563. -/
theorem noS8R164_Law4563 : ∀ v : Magma.tup8R164,
    ¬ @Equation4563 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4563) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4563) (by native_decide) v.1 v.2
    ((@Law4563.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4564 takes them (10 nodes). -/
def ordS8R164_Law4564 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4564. -/
theorem noS8R164_Law4564 : ∀ v : Magma.tup8R164,
    ¬ @Equation4564 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4564) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4564) (by native_decide) v.1 v.2
    ((@Law4564.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4565 takes them (6 nodes). -/
def ordS8R164_Law4565 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4565. -/
theorem noS8R164_Law4565 : ∀ v : Magma.tup8R164,
    ¬ @Equation4565 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4565) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4565) (by native_decide) v.1 v.2
    ((@Law4565.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4566 takes them (6 nodes). -/
def ordS8R164_Law4566 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4566. -/
theorem noS8R164_Law4566 : ∀ v : Magma.tup8R164,
    ¬ @Equation4566 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4566) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4566) (by native_decide) v.1 v.2
    ((@Law4566.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4567 takes them (7 nodes). -/
def ordS8R164_Law4567 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4567. -/
theorem noS8R164_Law4567 : ∀ v : Magma.tup8R164,
    ¬ @Equation4567 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4567) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4567) (by native_decide) v.1 v.2
    ((@Law4567.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4568 takes them (7 nodes). -/
def ordS8R164_Law4568 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4568. -/
theorem noS8R164_Law4568 : ∀ v : Magma.tup8R164,
    ¬ @Equation4568 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4568) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4568) (by native_decide) v.1 v.2
    ((@Law4568.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4569 takes them (10 nodes). -/
def ordS8R164_Law4569 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4569. -/
theorem noS8R164_Law4569 : ∀ v : Magma.tup8R164,
    ¬ @Equation4569 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4569) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4569) (by native_decide) v.1 v.2
    ((@Law4569.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4570 takes them (7 nodes). -/
def ordS8R164_Law4570 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4570. -/
theorem noS8R164_Law4570 : ∀ v : Magma.tup8R164,
    ¬ @Equation4570 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4570) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4570) (by native_decide) v.1 v.2
    ((@Law4570.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4571 takes them (6 nodes). -/
def ordS8R164_Law4571 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4571. -/
theorem noS8R164_Law4571 : ∀ v : Magma.tup8R164,
    ¬ @Equation4571 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4571) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4571) (by native_decide) v.1 v.2
    ((@Law4571.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `83` equations. -/
theorem srch8R164_refutes_15 :
    FamilyRefutes Magma.srch8R164 [
      4472, 4474, 4475, 4476, 4478, 4479, 4481, 4485, 4486, 4487, 4488, 4489, 4490, 4492, 4493,
      4494, 4495, 4496, 4501, 4502, 4503, 4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511, 4513,
      4514, 4516, 4517, 4518, 4519, 4520, 4521, 4522, 4523, 4524, 4526, 4527, 4528, 4529, 4530,
      4532, 4533, 4534, 4535, 4536, 4537, 4538, 4539, 4540, 4542, 4543, 4545, 4546, 4547, 4548,
      4549, 4550, 4551, 4552, 4553, 4554, 4555, 4556, 4557, 4558, 4559, 4560, 4561, 4562, 4563,
      4564, 4565, 4566, 4567, 4568, 4569, 4570, 4571
    ] :=
  ⟨noS8R164_Law4472, noS8R164_Law4474, noS8R164_Law4475, noS8R164_Law4476, noS8R164_Law4478, noS8R164_Law4479, noS8R164_Law4481, noS8R164_Law4485, noS8R164_Law4486, noS8R164_Law4487, noS8R164_Law4488, noS8R164_Law4489, noS8R164_Law4490, noS8R164_Law4492, noS8R164_Law4493, noS8R164_Law4494, noS8R164_Law4495, noS8R164_Law4496, noS8R164_Law4501, noS8R164_Law4502, noS8R164_Law4503, noS8R164_Law4504, noS8R164_Law4505, noS8R164_Law4506, noS8R164_Law4507, noS8R164_Law4508, noS8R164_Law4509, noS8R164_Law4510, noS8R164_Law4511, noS8R164_Law4513, noS8R164_Law4514, noS8R164_Law4516, noS8R164_Law4517, noS8R164_Law4518, noS8R164_Law4519, noS8R164_Law4520, noS8R164_Law4521, noS8R164_Law4522, noS8R164_Law4523, noS8R164_Law4524, noS8R164_Law4526, noS8R164_Law4527, noS8R164_Law4528, noS8R164_Law4529, noS8R164_Law4530, noS8R164_Law4532, noS8R164_Law4533, noS8R164_Law4534, noS8R164_Law4535, noS8R164_Law4536, noS8R164_Law4537, noS8R164_Law4538, noS8R164_Law4539, noS8R164_Law4540, noS8R164_Law4542, noS8R164_Law4543, noS8R164_Law4545, noS8R164_Law4546, noS8R164_Law4547, noS8R164_Law4548, noS8R164_Law4549, noS8R164_Law4550, noS8R164_Law4551, noS8R164_Law4552, noS8R164_Law4553, noS8R164_Law4554, noS8R164_Law4555, noS8R164_Law4556, noS8R164_Law4557, noS8R164_Law4558, noS8R164_Law4559, noS8R164_Law4560, noS8R164_Law4561, noS8R164_Law4562, noS8R164_Law4563, noS8R164_Law4564, noS8R164_Law4565, noS8R164_Law4566, noS8R164_Law4567, noS8R164_Law4568, noS8R164_Law4569, noS8R164_Law4570, noS8R164_Law4571⟩

import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 7 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `83` equations here, 634 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3538 takes them (9 nodes). -/
def ordS8R164_Law3538 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3538. -/
theorem noS8R164_Law3538 : ∀ v : Magma.tup8R164,
    ¬ @Equation3538 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3538) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3538) (by native_decide) v.1 v.2
    ((@Law3538.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3539 takes them (9 nodes). -/
def ordS8R164_Law3539 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3539. -/
theorem noS8R164_Law3539 : ∀ v : Magma.tup8R164,
    ¬ @Equation3539 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3539) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3539) (by native_decide) v.1 v.2
    ((@Law3539.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3540 takes them (9 nodes). -/
def ordS8R164_Law3540 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3540. -/
theorem noS8R164_Law3540 : ∀ v : Magma.tup8R164,
    ¬ @Equation3540 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3540) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3540) (by native_decide) v.1 v.2
    ((@Law3540.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3541 takes them (13 nodes). -/
def ordS8R164_Law3541 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3541. -/
theorem noS8R164_Law3541 : ∀ v : Magma.tup8R164,
    ¬ @Equation3541 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3541) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3541) (by native_decide) v.1 v.2
    ((@Law3541.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3542 takes them (9 nodes). -/
def ordS8R164_Law3542 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3542. -/
theorem noS8R164_Law3542 : ∀ v : Magma.tup8R164,
    ¬ @Equation3542 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3542) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3542) (by native_decide) v.1 v.2
    ((@Law3542.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3543 takes them (9 nodes). -/
def ordS8R164_Law3543 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3543. -/
theorem noS8R164_Law3543 : ∀ v : Magma.tup8R164,
    ¬ @Equation3543 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3543) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3543) (by native_decide) v.1 v.2
    ((@Law3543.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3544 takes them (9 nodes). -/
def ordS8R164_Law3544 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3544. -/
theorem noS8R164_Law3544 : ∀ v : Magma.tup8R164,
    ¬ @Equation3544 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3544) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3544) (by native_decide) v.1 v.2
    ((@Law3544.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3546 takes them (17 nodes). -/
def ordS8R164_Law3546 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3546. -/
theorem noS8R164_Law3546 : ∀ v : Magma.tup8R164,
    ¬ @Equation3546 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3546) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3546) (by native_decide) v.1 v.2
    ((@Law3546.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3547 takes them (6 nodes). -/
def ordS8R164_Law3547 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3547. -/
theorem noS8R164_Law3547 : ∀ v : Magma.tup8R164,
    ¬ @Equation3547 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3547) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3547) (by native_decide) v.1 v.2
    ((@Law3547.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3548 takes them (12 nodes). -/
def ordS8R164_Law3548 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3548. -/
theorem noS8R164_Law3548 : ∀ v : Magma.tup8R164,
    ¬ @Equation3548 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3548) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3548) (by native_decide) v.1 v.2
    ((@Law3548.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3550 takes them (6 nodes). -/
def ordS8R164_Law3550 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3550. -/
theorem noS8R164_Law3550 : ∀ v : Magma.tup8R164,
    ¬ @Equation3550 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3550) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3550) (by native_decide) v.1 v.2
    ((@Law3550.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3551 takes them (7 nodes). -/
def ordS8R164_Law3551 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3551. -/
theorem noS8R164_Law3551 : ∀ v : Magma.tup8R164,
    ¬ @Equation3551 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3551) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3551) (by native_decide) v.1 v.2
    ((@Law3551.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3552 takes them (10 nodes). -/
def ordS8R164_Law3552 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3552. -/
theorem noS8R164_Law3552 : ∀ v : Magma.tup8R164,
    ¬ @Equation3552 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3552) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3552) (by native_decide) v.1 v.2
    ((@Law3552.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3554 takes them (6 nodes). -/
def ordS8R164_Law3554 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3554. -/
theorem noS8R164_Law3554 : ∀ v : Magma.tup8R164,
    ¬ @Equation3554 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3554) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3554) (by native_decide) v.1 v.2
    ((@Law3554.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3555 takes them (12 nodes). -/
def ordS8R164_Law3555 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3555. -/
theorem noS8R164_Law3555 : ∀ v : Magma.tup8R164,
    ¬ @Equation3555 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3555) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3555) (by native_decide) v.1 v.2
    ((@Law3555.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3557 takes them (6 nodes). -/
def ordS8R164_Law3557 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3557. -/
theorem noS8R164_Law3557 : ∀ v : Magma.tup8R164,
    ¬ @Equation3557 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3557) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3557) (by native_decide) v.1 v.2
    ((@Law3557.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3559 takes them (10 nodes). -/
def ordS8R164_Law3559 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3559. -/
theorem noS8R164_Law3559 : ∀ v : Magma.tup8R164,
    ¬ @Equation3559 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3559) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3559) (by native_decide) v.1 v.2
    ((@Law3559.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3560 takes them (6 nodes). -/
def ordS8R164_Law3560 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3560. -/
theorem noS8R164_Law3560 : ∀ v : Magma.tup8R164,
    ¬ @Equation3560 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3560) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3560) (by native_decide) v.1 v.2
    ((@Law3560.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3561 takes them (7 nodes). -/
def ordS8R164_Law3561 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3561. -/
theorem noS8R164_Law3561 : ∀ v : Magma.tup8R164,
    ¬ @Equation3561 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3561) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3561) (by native_decide) v.1 v.2
    ((@Law3561.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3562 takes them (10 nodes). -/
def ordS8R164_Law3562 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3562. -/
theorem noS8R164_Law3562 : ∀ v : Magma.tup8R164,
    ¬ @Equation3562 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3562) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3562) (by native_decide) v.1 v.2
    ((@Law3562.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3563 takes them (7 nodes). -/
def ordS8R164_Law3563 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3563. -/
theorem noS8R164_Law3563 : ∀ v : Magma.tup8R164,
    ¬ @Equation3563 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3563) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3563) (by native_decide) v.1 v.2
    ((@Law3563.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3564 takes them (6 nodes). -/
def ordS8R164_Law3564 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3564. -/
theorem noS8R164_Law3564 : ∀ v : Magma.tup8R164,
    ¬ @Equation3564 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3564) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3564) (by native_decide) v.1 v.2
    ((@Law3564.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3565 takes them (7 nodes). -/
def ordS8R164_Law3565 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3565. -/
theorem noS8R164_Law3565 : ∀ v : Magma.tup8R164,
    ¬ @Equation3565 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3565) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3565) (by native_decide) v.1 v.2
    ((@Law3565.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3566 takes them (10 nodes). -/
def ordS8R164_Law3566 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3566. -/
theorem noS8R164_Law3566 : ∀ v : Magma.tup8R164,
    ¬ @Equation3566 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3566) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3566) (by native_decide) v.1 v.2
    ((@Law3566.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3568 takes them (6 nodes). -/
def ordS8R164_Law3568 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3568. -/
theorem noS8R164_Law3568 : ∀ v : Magma.tup8R164,
    ¬ @Equation3568 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3568) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3568) (by native_decide) v.1 v.2
    ((@Law3568.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3569 takes them (7 nodes). -/
def ordS8R164_Law3569 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3569. -/
theorem noS8R164_Law3569 : ∀ v : Magma.tup8R164,
    ¬ @Equation3569 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3569) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3569) (by native_decide) v.1 v.2
    ((@Law3569.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3570 takes them (10 nodes). -/
def ordS8R164_Law3570 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3570. -/
theorem noS8R164_Law3570 : ∀ v : Magma.tup8R164,
    ¬ @Equation3570 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3570) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3570) (by native_decide) v.1 v.2
    ((@Law3570.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3571 takes them (7 nodes). -/
def ordS8R164_Law3571 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3571. -/
theorem noS8R164_Law3571 : ∀ v : Magma.tup8R164,
    ¬ @Equation3571 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3571) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3571) (by native_decide) v.1 v.2
    ((@Law3571.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3572 takes them (6 nodes). -/
def ordS8R164_Law3572 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3572. -/
theorem noS8R164_Law3572 : ∀ v : Magma.tup8R164,
    ¬ @Equation3572 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3572) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3572) (by native_decide) v.1 v.2
    ((@Law3572.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3574 takes them (10 nodes). -/
def ordS8R164_Law3574 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3574. -/
theorem noS8R164_Law3574 : ∀ v : Magma.tup8R164,
    ¬ @Equation3574 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3574) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3574) (by native_decide) v.1 v.2
    ((@Law3574.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3575 takes them (7 nodes). -/
def ordS8R164_Law3575 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3575. -/
theorem noS8R164_Law3575 : ∀ v : Magma.tup8R164,
    ¬ @Equation3575 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3575) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3575) (by native_decide) v.1 v.2
    ((@Law3575.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3576 takes them (6 nodes). -/
def ordS8R164_Law3576 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3576. -/
theorem noS8R164_Law3576 : ∀ v : Magma.tup8R164,
    ¬ @Equation3576 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3576) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3576) (by native_decide) v.1 v.2
    ((@Law3576.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3577 takes them (7 nodes). -/
def ordS8R164_Law3577 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3577. -/
theorem noS8R164_Law3577 : ∀ v : Magma.tup8R164,
    ¬ @Equation3577 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3577) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3577) (by native_decide) v.1 v.2
    ((@Law3577.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3578 takes them (10 nodes). -/
def ordS8R164_Law3578 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3578. -/
theorem noS8R164_Law3578 : ∀ v : Magma.tup8R164,
    ¬ @Equation3578 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3578) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3578) (by native_decide) v.1 v.2
    ((@Law3578.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3579 takes them (7 nodes). -/
def ordS8R164_Law3579 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3579. -/
theorem noS8R164_Law3579 : ∀ v : Magma.tup8R164,
    ¬ @Equation3579 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3579) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3579) (by native_decide) v.1 v.2
    ((@Law3579.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3580 takes them (7 nodes). -/
def ordS8R164_Law3580 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3580. -/
theorem noS8R164_Law3580 : ∀ v : Magma.tup8R164,
    ¬ @Equation3580 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3580) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3580) (by native_decide) v.1 v.2
    ((@Law3580.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3581 takes them (6 nodes). -/
def ordS8R164_Law3581 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3581. -/
theorem noS8R164_Law3581 : ∀ v : Magma.tup8R164,
    ¬ @Equation3581 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3581) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3581) (by native_decide) v.1 v.2
    ((@Law3581.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3582 takes them (6 nodes). -/
def ordS8R164_Law3582 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3582. -/
theorem noS8R164_Law3582 : ∀ v : Magma.tup8R164,
    ¬ @Equation3582 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3582) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3582) (by native_decide) v.1 v.2
    ((@Law3582.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3583 takes them (10 nodes). -/
def ordS8R164_Law3583 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3583. -/
theorem noS8R164_Law3583 : ∀ v : Magma.tup8R164,
    ¬ @Equation3583 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3583) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3583) (by native_decide) v.1 v.2
    ((@Law3583.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3584 takes them (6 nodes). -/
def ordS8R164_Law3584 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3584. -/
theorem noS8R164_Law3584 : ∀ v : Magma.tup8R164,
    ¬ @Equation3584 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3584) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3584) (by native_decide) v.1 v.2
    ((@Law3584.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3585 takes them (6 nodes). -/
def ordS8R164_Law3585 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3585. -/
theorem noS8R164_Law3585 : ∀ v : Magma.tup8R164,
    ¬ @Equation3585 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3585) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3585) (by native_decide) v.1 v.2
    ((@Law3585.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3586 takes them (7 nodes). -/
def ordS8R164_Law3586 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3586. -/
theorem noS8R164_Law3586 : ∀ v : Magma.tup8R164,
    ¬ @Equation3586 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3586) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3586) (by native_decide) v.1 v.2
    ((@Law3586.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3587 takes them (10 nodes). -/
def ordS8R164_Law3587 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3587. -/
theorem noS8R164_Law3587 : ∀ v : Magma.tup8R164,
    ¬ @Equation3587 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3587) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3587) (by native_decide) v.1 v.2
    ((@Law3587.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3589 takes them (6 nodes). -/
def ordS8R164_Law3589 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3589. -/
theorem noS8R164_Law3589 : ∀ v : Magma.tup8R164,
    ¬ @Equation3589 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3589) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3589) (by native_decide) v.1 v.2
    ((@Law3589.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3590 takes them (6 nodes). -/
def ordS8R164_Law3590 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3590. -/
theorem noS8R164_Law3590 : ∀ v : Magma.tup8R164,
    ¬ @Equation3590 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3590) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3590) (by native_decide) v.1 v.2
    ((@Law3590.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3592 takes them (6 nodes). -/
def ordS8R164_Law3592 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3592. -/
theorem noS8R164_Law3592 : ∀ v : Magma.tup8R164,
    ¬ @Equation3592 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3592) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3592) (by native_decide) v.1 v.2
    ((@Law3592.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3593 takes them (6 nodes). -/
def ordS8R164_Law3593 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3593. -/
theorem noS8R164_Law3593 : ∀ v : Magma.tup8R164,
    ¬ @Equation3593 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3593) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3593) (by native_decide) v.1 v.2
    ((@Law3593.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3594 takes them (6 nodes). -/
def ordS8R164_Law3594 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3594. -/
theorem noS8R164_Law3594 : ∀ v : Magma.tup8R164,
    ¬ @Equation3594 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3594) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3594) (by native_decide) v.1 v.2
    ((@Law3594.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3595 takes them (10 nodes). -/
def ordS8R164_Law3595 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3595. -/
theorem noS8R164_Law3595 : ∀ v : Magma.tup8R164,
    ¬ @Equation3595 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3595) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3595) (by native_decide) v.1 v.2
    ((@Law3595.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3596 takes them (6 nodes). -/
def ordS8R164_Law3596 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3596. -/
theorem noS8R164_Law3596 : ∀ v : Magma.tup8R164,
    ¬ @Equation3596 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3596) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3596) (by native_decide) v.1 v.2
    ((@Law3596.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3597 takes them (6 nodes). -/
def ordS8R164_Law3597 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3597. -/
theorem noS8R164_Law3597 : ∀ v : Magma.tup8R164,
    ¬ @Equation3597 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3597) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3597) (by native_decide) v.1 v.2
    ((@Law3597.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3598 takes them (6 nodes). -/
def ordS8R164_Law3598 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3598. -/
theorem noS8R164_Law3598 : ∀ v : Magma.tup8R164,
    ¬ @Equation3598 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3598) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3598) (by native_decide) v.1 v.2
    ((@Law3598.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3599 takes them (7 nodes). -/
def ordS8R164_Law3599 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3599. -/
theorem noS8R164_Law3599 : ∀ v : Magma.tup8R164,
    ¬ @Equation3599 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3599) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3599) (by native_decide) v.1 v.2
    ((@Law3599.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3600 takes them (10 nodes). -/
def ordS8R164_Law3600 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3600. -/
theorem noS8R164_Law3600 : ∀ v : Magma.tup8R164,
    ¬ @Equation3600 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3600) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3600) (by native_decide) v.1 v.2
    ((@Law3600.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3602 takes them (6 nodes). -/
def ordS8R164_Law3602 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3602. -/
theorem noS8R164_Law3602 : ∀ v : Magma.tup8R164,
    ¬ @Equation3602 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3602) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3602) (by native_decide) v.1 v.2
    ((@Law3602.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3603 takes them (7 nodes). -/
def ordS8R164_Law3603 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3603. -/
theorem noS8R164_Law3603 : ∀ v : Magma.tup8R164,
    ¬ @Equation3603 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3603) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3603) (by native_decide) v.1 v.2
    ((@Law3603.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3604 takes them (10 nodes). -/
def ordS8R164_Law3604 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3604. -/
theorem noS8R164_Law3604 : ∀ v : Magma.tup8R164,
    ¬ @Equation3604 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3604) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3604) (by native_decide) v.1 v.2
    ((@Law3604.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3605 takes them (8 nodes). -/
def ordS8R164_Law3605 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3605. -/
theorem noS8R164_Law3605 : ∀ v : Magma.tup8R164,
    ¬ @Equation3605 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3605) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3605) (by native_decide) v.1 v.2
    ((@Law3605.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3606 takes them (6 nodes). -/
def ordS8R164_Law3606 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3606. -/
theorem noS8R164_Law3606 : ∀ v : Magma.tup8R164,
    ¬ @Equation3606 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3606) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3606) (by native_decide) v.1 v.2
    ((@Law3606.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3608 takes them (10 nodes). -/
def ordS8R164_Law3608 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3608. -/
theorem noS8R164_Law3608 : ∀ v : Magma.tup8R164,
    ¬ @Equation3608 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3608) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3608) (by native_decide) v.1 v.2
    ((@Law3608.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3609 takes them (7 nodes). -/
def ordS8R164_Law3609 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3609. -/
theorem noS8R164_Law3609 : ∀ v : Magma.tup8R164,
    ¬ @Equation3609 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3609) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3609) (by native_decide) v.1 v.2
    ((@Law3609.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3610 takes them (6 nodes). -/
def ordS8R164_Law3610 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3610. -/
theorem noS8R164_Law3610 : ∀ v : Magma.tup8R164,
    ¬ @Equation3610 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3610) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3610) (by native_decide) v.1 v.2
    ((@Law3610.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3611 takes them (7 nodes). -/
def ordS8R164_Law3611 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3611. -/
theorem noS8R164_Law3611 : ∀ v : Magma.tup8R164,
    ¬ @Equation3611 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3611) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3611) (by native_decide) v.1 v.2
    ((@Law3611.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3612 takes them (10 nodes). -/
def ordS8R164_Law3612 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3612. -/
theorem noS8R164_Law3612 : ∀ v : Magma.tup8R164,
    ¬ @Equation3612 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3612) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3612) (by native_decide) v.1 v.2
    ((@Law3612.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3613 takes them (7 nodes). -/
def ordS8R164_Law3613 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3613. -/
theorem noS8R164_Law3613 : ∀ v : Magma.tup8R164,
    ¬ @Equation3613 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3613) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3613) (by native_decide) v.1 v.2
    ((@Law3613.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3614 takes them (7 nodes). -/
def ordS8R164_Law3614 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3614. -/
theorem noS8R164_Law3614 : ∀ v : Magma.tup8R164,
    ¬ @Equation3614 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3614) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3614) (by native_decide) v.1 v.2
    ((@Law3614.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3615 takes them (6 nodes). -/
def ordS8R164_Law3615 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3615. -/
theorem noS8R164_Law3615 : ∀ v : Magma.tup8R164,
    ¬ @Equation3615 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3615) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3615) (by native_decide) v.1 v.2
    ((@Law3615.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3616 takes them (6 nodes). -/
def ordS8R164_Law3616 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3616. -/
theorem noS8R164_Law3616 : ∀ v : Magma.tup8R164,
    ¬ @Equation3616 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3616) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3616) (by native_decide) v.1 v.2
    ((@Law3616.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3618 takes them (6 nodes). -/
def ordS8R164_Law3618 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3618. -/
theorem noS8R164_Law3618 : ∀ v : Magma.tup8R164,
    ¬ @Equation3618 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3618) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3618) (by native_decide) v.1 v.2
    ((@Law3618.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3619 takes them (6 nodes). -/
def ordS8R164_Law3619 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3619. -/
theorem noS8R164_Law3619 : ∀ v : Magma.tup8R164,
    ¬ @Equation3619 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3619) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3619) (by native_decide) v.1 v.2
    ((@Law3619.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3621 takes them (10 nodes). -/
def ordS8R164_Law3621 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3621. -/
theorem noS8R164_Law3621 : ∀ v : Magma.tup8R164,
    ¬ @Equation3621 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3621) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3621) (by native_decide) v.1 v.2
    ((@Law3621.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3622 takes them (7 nodes). -/
def ordS8R164_Law3622 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3622. -/
theorem noS8R164_Law3622 : ∀ v : Magma.tup8R164,
    ¬ @Equation3622 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3622) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3622) (by native_decide) v.1 v.2
    ((@Law3622.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3623 takes them (6 nodes). -/
def ordS8R164_Law3623 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3623. -/
theorem noS8R164_Law3623 : ∀ v : Magma.tup8R164,
    ¬ @Equation3623 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3623) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3623) (by native_decide) v.1 v.2
    ((@Law3623.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3624 takes them (6 nodes). -/
def ordS8R164_Law3624 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3624. -/
theorem noS8R164_Law3624 : ∀ v : Magma.tup8R164,
    ¬ @Equation3624 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3624) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3624) (by native_decide) v.1 v.2
    ((@Law3624.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3625 takes them (10 nodes). -/
def ordS8R164_Law3625 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3625. -/
theorem noS8R164_Law3625 : ∀ v : Magma.tup8R164,
    ¬ @Equation3625 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3625) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3625) (by native_decide) v.1 v.2
    ((@Law3625.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3626 takes them (6 nodes). -/
def ordS8R164_Law3626 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3626. -/
theorem noS8R164_Law3626 : ∀ v : Magma.tup8R164,
    ¬ @Equation3626 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3626) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3626) (by native_decide) v.1 v.2
    ((@Law3626.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3627 takes them (6 nodes). -/
def ordS8R164_Law3627 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3627. -/
theorem noS8R164_Law3627 : ∀ v : Magma.tup8R164,
    ¬ @Equation3627 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3627) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3627) (by native_decide) v.1 v.2
    ((@Law3627.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3628 takes them (6 nodes). -/
def ordS8R164_Law3628 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3628. -/
theorem noS8R164_Law3628 : ∀ v : Magma.tup8R164,
    ¬ @Equation3628 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3628) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3628) (by native_decide) v.1 v.2
    ((@Law3628.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3629 takes them (10 nodes). -/
def ordS8R164_Law3629 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3629. -/
theorem noS8R164_Law3629 : ∀ v : Magma.tup8R164,
    ¬ @Equation3629 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3629) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3629) (by native_decide) v.1 v.2
    ((@Law3629.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3630 takes them (6 nodes). -/
def ordS8R164_Law3630 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3630. -/
theorem noS8R164_Law3630 : ∀ v : Magma.tup8R164,
    ¬ @Equation3630 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3630) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3630) (by native_decide) v.1 v.2
    ((@Law3630.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3631 takes them (6 nodes). -/
def ordS8R164_Law3631 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3631. -/
theorem noS8R164_Law3631 : ∀ v : Magma.tup8R164,
    ¬ @Equation3631 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3631) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3631) (by native_decide) v.1 v.2
    ((@Law3631.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3632 takes them (6 nodes). -/
def ordS8R164_Law3632 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3632. -/
theorem noS8R164_Law3632 : ∀ v : Magma.tup8R164,
    ¬ @Equation3632 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3632) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3632) (by native_decide) v.1 v.2
    ((@Law3632.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3633 takes them (6 nodes). -/
def ordS8R164_Law3633 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3633. -/
theorem noS8R164_Law3633 : ∀ v : Magma.tup8R164,
    ¬ @Equation3633 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3633) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3633) (by native_decide) v.1 v.2
    ((@Law3633.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `83` equations. -/
theorem srch8R164_refutes_6 :
    FamilyRefutes Magma.srch8R164 [
      3538, 3539, 3540, 3541, 3542, 3543, 3544, 3546, 3547, 3548, 3550, 3551, 3552, 3554, 3555,
      3557, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3568, 3569, 3570, 3571, 3572, 3574,
      3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3589, 3590,
      3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3602, 3603, 3604, 3605, 3606, 3608,
      3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3618, 3619, 3621, 3622, 3623, 3624, 3625,
      3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633
    ] :=
  ⟨noS8R164_Law3538, noS8R164_Law3539, noS8R164_Law3540, noS8R164_Law3541, noS8R164_Law3542, noS8R164_Law3543, noS8R164_Law3544, noS8R164_Law3546, noS8R164_Law3547, noS8R164_Law3548, noS8R164_Law3550, noS8R164_Law3551, noS8R164_Law3552, noS8R164_Law3554, noS8R164_Law3555, noS8R164_Law3557, noS8R164_Law3559, noS8R164_Law3560, noS8R164_Law3561, noS8R164_Law3562, noS8R164_Law3563, noS8R164_Law3564, noS8R164_Law3565, noS8R164_Law3566, noS8R164_Law3568, noS8R164_Law3569, noS8R164_Law3570, noS8R164_Law3571, noS8R164_Law3572, noS8R164_Law3574, noS8R164_Law3575, noS8R164_Law3576, noS8R164_Law3577, noS8R164_Law3578, noS8R164_Law3579, noS8R164_Law3580, noS8R164_Law3581, noS8R164_Law3582, noS8R164_Law3583, noS8R164_Law3584, noS8R164_Law3585, noS8R164_Law3586, noS8R164_Law3587, noS8R164_Law3589, noS8R164_Law3590, noS8R164_Law3592, noS8R164_Law3593, noS8R164_Law3594, noS8R164_Law3595, noS8R164_Law3596, noS8R164_Law3597, noS8R164_Law3598, noS8R164_Law3599, noS8R164_Law3600, noS8R164_Law3602, noS8R164_Law3603, noS8R164_Law3604, noS8R164_Law3605, noS8R164_Law3606, noS8R164_Law3608, noS8R164_Law3609, noS8R164_Law3610, noS8R164_Law3611, noS8R164_Law3612, noS8R164_Law3613, noS8R164_Law3614, noS8R164_Law3615, noS8R164_Law3616, noS8R164_Law3618, noS8R164_Law3619, noS8R164_Law3621, noS8R164_Law3622, noS8R164_Law3623, noS8R164_Law3624, noS8R164_Law3625, noS8R164_Law3626, noS8R164_Law3627, noS8R164_Law3628, noS8R164_Law3629, noS8R164_Law3630, noS8R164_Law3631, noS8R164_Law3632, noS8R164_Law3633⟩

import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 35 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `28`
equations here, 2,340 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3451 takes them (55 nodes). -/
def ordS6A_Law3451 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3451. -/
theorem noS6A_Law3451 : ∀ v : Magma.tupS6A,
    ¬ @Equation3451 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3451) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3451) (by native_decide) v.1 v.2
    ((@Law3451.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3452 takes them (12 nodes). -/
def ordS6A_Law3452 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3452. -/
theorem noS6A_Law3452 : ∀ v : Magma.tupS6A,
    ¬ @Equation3452 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3452) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3452) (by native_decide) v.1 v.2
    ((@Law3452.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3453 takes them (12 nodes). -/
def ordS6A_Law3453 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3453. -/
theorem noS6A_Law3453 : ∀ v : Magma.tupS6A,
    ¬ @Equation3453 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3453) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3453) (by native_decide) v.1 v.2
    ((@Law3453.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3454 takes them (12 nodes). -/
def ordS6A_Law3454 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3454. -/
theorem noS6A_Law3454 : ∀ v : Magma.tupS6A,
    ¬ @Equation3454 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3454) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3454) (by native_decide) v.1 v.2
    ((@Law3454.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3455 takes them (12 nodes). -/
def ordS6A_Law3455 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3455. -/
theorem noS6A_Law3455 : ∀ v : Magma.tupS6A,
    ¬ @Equation3455 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3455) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 6)
    (ord := ordS6A_Law3455) (by native_decide) v.1 v.2
    ((@Law3455.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3508 takes them (194 nodes). -/
def ordS6A_Law3508 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3508. -/
theorem noS6A_Law3508 : ∀ v : Magma.tupS6A,
    ¬ @Equation3508 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3508) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3508) (by native_decide) v.1 v.2
    ((@Law3508.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3510 takes them (160 nodes). -/
def ordS6A_Law3510 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3510. -/
theorem noS6A_Law3510 : ∀ v : Magma.tupS6A,
    ¬ @Equation3510 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3510) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3510) (by native_decide) v.1 v.2
    ((@Law3510.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3514 takes them (63 nodes). -/
def ordS6A_Law3514 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3514. -/
theorem noS6A_Law3514 : ∀ v : Magma.tupS6A,
    ¬ @Equation3514 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3514) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3514) (by native_decide) v.1 v.2
    ((@Law3514.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3516 takes them (57 nodes). -/
def ordS6A_Law3516 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3516. -/
theorem noS6A_Law3516 : ∀ v : Magma.tupS6A,
    ¬ @Equation3516 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3516) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3516) (by native_decide) v.1 v.2
    ((@Law3516.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3517 takes them (57 nodes). -/
def ordS6A_Law3517 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3517. -/
theorem noS6A_Law3517 : ∀ v : Magma.tupS6A,
    ¬ @Equation3517 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3517) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3517) (by native_decide) v.1 v.2
    ((@Law3517.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3528 takes them (84 nodes). -/
def ordS6A_Law3528 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3528. -/
theorem noS6A_Law3528 : ∀ v : Magma.tupS6A,
    ¬ @Equation3528 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3528) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3528) (by native_decide) v.1 v.2
    ((@Law3528.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3530 takes them (83 nodes). -/
def ordS6A_Law3530 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3530. -/
theorem noS6A_Law3530 : ∀ v : Magma.tupS6A,
    ¬ @Equation3530 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3530) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3530) (by native_decide) v.1 v.2
    ((@Law3530.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3531 takes them (83 nodes). -/
def ordS6A_Law3531 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3531. -/
theorem noS6A_Law3531 : ∀ v : Magma.tupS6A,
    ¬ @Equation3531 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3531) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3531) (by native_decide) v.1 v.2
    ((@Law3531.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3532 takes them (100 nodes). -/
def ordS6A_Law3532 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3532. -/
theorem noS6A_Law3532 : ∀ v : Magma.tupS6A,
    ¬ @Equation3532 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3532) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3532) (by native_decide) v.1 v.2
    ((@Law3532.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3535 takes them (57 nodes). -/
def ordS6A_Law3535 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3535. -/
theorem noS6A_Law3535 : ∀ v : Magma.tupS6A,
    ¬ @Equation3535 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3535) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3535) (by native_decide) v.1 v.2
    ((@Law3535.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3536 takes them (126 nodes). -/
def ordS6A_Law3536 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3536. -/
theorem noS6A_Law3536 : ∀ v : Magma.tupS6A,
    ¬ @Equation3536 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3536) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3536) (by native_decide) v.1 v.2
    ((@Law3536.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3538 takes them (125 nodes). -/
def ordS6A_Law3538 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3538. -/
theorem noS6A_Law3538 : ∀ v : Magma.tupS6A,
    ¬ @Equation3538 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3538) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3538) (by native_decide) v.1 v.2
    ((@Law3538.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3539 takes them (125 nodes). -/
def ordS6A_Law3539 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3539. -/
theorem noS6A_Law3539 : ∀ v : Magma.tupS6A,
    ¬ @Equation3539 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3539) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3539) (by native_decide) v.1 v.2
    ((@Law3539.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3540 takes them (53 nodes). -/
def ordS6A_Law3540 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3540. -/
theorem noS6A_Law3540 : ∀ v : Magma.tupS6A,
    ¬ @Equation3540 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3540) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3540) (by native_decide) v.1 v.2
    ((@Law3540.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3542 takes them (52 nodes). -/
def ordS6A_Law3542 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3542. -/
theorem noS6A_Law3542 : ∀ v : Magma.tupS6A,
    ¬ @Equation3542 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3542) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3542) (by native_decide) v.1 v.2
    ((@Law3542.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3543 takes them (52 nodes). -/
def ordS6A_Law3543 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3543. -/
theorem noS6A_Law3543 : ∀ v : Magma.tupS6A,
    ¬ @Equation3543 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3543) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3543) (by native_decide) v.1 v.2
    ((@Law3543.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3544 takes them (52 nodes). -/
def ordS6A_Law3544 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3544. -/
theorem noS6A_Law3544 : ∀ v : Magma.tupS6A,
    ¬ @Equation3544 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3544) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3544) (by native_decide) v.1 v.2
    ((@Law3544.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3547 takes them (152 nodes). -/
def ordS6A_Law3547 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3547. -/
theorem noS6A_Law3547 : ∀ v : Magma.tupS6A,
    ¬ @Equation3547 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3547) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3547) (by native_decide) v.1 v.2
    ((@Law3547.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3550 takes them (123 nodes). -/
def ordS6A_Law3550 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3550. -/
theorem noS6A_Law3550 : ∀ v : Magma.tupS6A,
    ¬ @Equation3550 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3550) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3550) (by native_decide) v.1 v.2
    ((@Law3550.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3551 takes them (96 nodes). -/
def ordS6A_Law3551 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3551. -/
theorem noS6A_Law3551 : ∀ v : Magma.tupS6A,
    ¬ @Equation3551 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3551) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3551) (by native_decide) v.1 v.2
    ((@Law3551.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3552 takes them (150 nodes). -/
def ordS6A_Law3552 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3552. -/
theorem noS6A_Law3552 : ∀ v : Magma.tupS6A,
    ¬ @Equation3552 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3552) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3552) (by native_decide) v.1 v.2
    ((@Law3552.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3553 takes them (149 nodes). -/
def ordS6A_Law3553 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3553. -/
theorem noS6A_Law3553 : ∀ v : Magma.tupS6A,
    ¬ @Equation3553 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3553) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3553) (by native_decide) v.1 v.2
    ((@Law3553.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3554 takes them (44 nodes). -/
def ordS6A_Law3554 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3554. -/
theorem noS6A_Law3554 : ∀ v : Magma.tupS6A,
    ¬ @Equation3554 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3554) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3554) (by native_decide) v.1 v.2
    ((@Law3554.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `28` equations. -/
theorem srch6A_refutes_34 :
    FamilyRefutes Magma.srch6A [
      3451, 3452, 3453, 3454, 3455, 3508, 3510, 3514, 3516, 3517, 3528, 3530, 3531, 3532, 3535,
      3536, 3538, 3539, 3540, 3542, 3543, 3544, 3547, 3550, 3551, 3552, 3553, 3554
    ] :=
  ⟨noS6A_Law3451, noS6A_Law3452, noS6A_Law3453, noS6A_Law3454, noS6A_Law3455, noS6A_Law3508, noS6A_Law3510, noS6A_Law3514, noS6A_Law3516, noS6A_Law3517, noS6A_Law3528, noS6A_Law3530, noS6A_Law3531, noS6A_Law3532, noS6A_Law3535, noS6A_Law3536, noS6A_Law3538, noS6A_Law3539, noS6A_Law3540, noS6A_Law3542, noS6A_Law3543, noS6A_Law3544, noS6A_Law3547, noS6A_Law3550, noS6A_Law3551, noS6A_Law3552, noS6A_Law3553, noS6A_Law3554⟩

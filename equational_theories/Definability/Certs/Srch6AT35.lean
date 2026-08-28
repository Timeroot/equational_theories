import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 36 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `21`
equations here, 3,060 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3555 takes them (548 nodes). -/
def ordS6A_Law3555 : List (Fin 11) := [10, 8, 1, 6, 9, 3, 0, 4, 7, 2, 5]

/-- No member of the class satisfies equation 3555. -/
theorem noS6A_Law3555 : ∀ v : Magma.tupS6A,
    ¬ @Equation3555 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3555) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3555) (by native_decide) v.1 v.2
    ((@Law3555.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3557 takes them (128 nodes). -/
def ordS6A_Law3557 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3557. -/
theorem noS6A_Law3557 : ∀ v : Magma.tupS6A,
    ¬ @Equation3557 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3557) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3557) (by native_decide) v.1 v.2
    ((@Law3557.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3559 takes them (299 nodes). -/
def ordS6A_Law3559 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3559. -/
theorem noS6A_Law3559 : ∀ v : Magma.tupS6A,
    ¬ @Equation3559 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3559) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3559) (by native_decide) v.1 v.2
    ((@Law3559.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3560 takes them (122 nodes). -/
def ordS6A_Law3560 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3560. -/
theorem noS6A_Law3560 : ∀ v : Magma.tupS6A,
    ¬ @Equation3560 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3560) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3560) (by native_decide) v.1 v.2
    ((@Law3560.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3561 takes them (80 nodes). -/
def ordS6A_Law3561 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3561. -/
theorem noS6A_Law3561 : ∀ v : Magma.tupS6A,
    ¬ @Equation3561 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3561) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3561) (by native_decide) v.1 v.2
    ((@Law3561.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3562 takes them (162 nodes). -/
def ordS6A_Law3562 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3562. -/
theorem noS6A_Law3562 : ∀ v : Magma.tupS6A,
    ¬ @Equation3562 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3562) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3562) (by native_decide) v.1 v.2
    ((@Law3562.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3563 takes them (80 nodes). -/
def ordS6A_Law3563 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3563. -/
theorem noS6A_Law3563 : ∀ v : Magma.tupS6A,
    ¬ @Equation3563 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3563) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3563) (by native_decide) v.1 v.2
    ((@Law3563.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3564 takes them (47 nodes). -/
def ordS6A_Law3564 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3564. -/
theorem noS6A_Law3564 : ∀ v : Magma.tupS6A,
    ¬ @Equation3564 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3564) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3564) (by native_decide) v.1 v.2
    ((@Law3564.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3565 takes them (126 nodes). -/
def ordS6A_Law3565 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3565. -/
theorem noS6A_Law3565 : ∀ v : Magma.tupS6A,
    ¬ @Equation3565 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3565) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3565) (by native_decide) v.1 v.2
    ((@Law3565.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3567 takes them (197 nodes). -/
def ordS6A_Law3567 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3567. -/
theorem noS6A_Law3567 : ∀ v : Magma.tupS6A,
    ¬ @Equation3567 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3567) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3567) (by native_decide) v.1 v.2
    ((@Law3567.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3568 takes them (75 nodes). -/
def ordS6A_Law3568 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3568. -/
theorem noS6A_Law3568 : ∀ v : Magma.tupS6A,
    ¬ @Equation3568 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3568) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3568) (by native_decide) v.1 v.2
    ((@Law3568.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3569 takes them (107 nodes). -/
def ordS6A_Law3569 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3569. -/
theorem noS6A_Law3569 : ∀ v : Magma.tupS6A,
    ¬ @Equation3569 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3569) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3569) (by native_decide) v.1 v.2
    ((@Law3569.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3570 takes them (177 nodes). -/
def ordS6A_Law3570 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3570. -/
theorem noS6A_Law3570 : ∀ v : Magma.tupS6A,
    ¬ @Equation3570 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3570) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3570) (by native_decide) v.1 v.2
    ((@Law3570.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3571 takes them (90 nodes). -/
def ordS6A_Law3571 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3571. -/
theorem noS6A_Law3571 : ∀ v : Magma.tupS6A,
    ¬ @Equation3571 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3571) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3571) (by native_decide) v.1 v.2
    ((@Law3571.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3572 takes them (72 nodes). -/
def ordS6A_Law3572 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3572. -/
theorem noS6A_Law3572 : ∀ v : Magma.tupS6A,
    ¬ @Equation3572 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3572) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3572) (by native_decide) v.1 v.2
    ((@Law3572.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3574 takes them (232 nodes). -/
def ordS6A_Law3574 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3574. -/
theorem noS6A_Law3574 : ∀ v : Magma.tupS6A,
    ¬ @Equation3574 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3574) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3574) (by native_decide) v.1 v.2
    ((@Law3574.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3575 takes them (142 nodes). -/
def ordS6A_Law3575 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3575. -/
theorem noS6A_Law3575 : ∀ v : Magma.tupS6A,
    ¬ @Equation3575 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3575) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3575) (by native_decide) v.1 v.2
    ((@Law3575.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3576 takes them (117 nodes). -/
def ordS6A_Law3576 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3576. -/
theorem noS6A_Law3576 : ∀ v : Magma.tupS6A,
    ¬ @Equation3576 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3576) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3576) (by native_decide) v.1 v.2
    ((@Law3576.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3577 takes them (62 nodes). -/
def ordS6A_Law3577 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3577. -/
theorem noS6A_Law3577 : ∀ v : Magma.tupS6A,
    ¬ @Equation3577 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3577) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3577) (by native_decide) v.1 v.2
    ((@Law3577.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3578 takes them (137 nodes). -/
def ordS6A_Law3578 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3578. -/
theorem noS6A_Law3578 : ∀ v : Magma.tupS6A,
    ¬ @Equation3578 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3578) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3578) (by native_decide) v.1 v.2
    ((@Law3578.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3579 takes them (60 nodes). -/
def ordS6A_Law3579 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3579. -/
theorem noS6A_Law3579 : ∀ v : Magma.tupS6A,
    ¬ @Equation3579 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3579) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3579) (by native_decide) v.1 v.2
    ((@Law3579.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `21` equations. -/
theorem srch6A_refutes_35 :
    FamilyRefutes Magma.srch6A [
      3555, 3557, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3567, 3568, 3569, 3570, 3571, 3572,
      3574, 3575, 3576, 3577, 3578, 3579
    ] :=
  ⟨noS6A_Law3555, noS6A_Law3557, noS6A_Law3559, noS6A_Law3560, noS6A_Law3561, noS6A_Law3562, noS6A_Law3563, noS6A_Law3564, noS6A_Law3565, noS6A_Law3567, noS6A_Law3568, noS6A_Law3569, noS6A_Law3570, noS6A_Law3571, noS6A_Law3572, noS6A_Law3574, noS6A_Law3575, noS6A_Law3576, noS6A_Law3577, noS6A_Law3578, noS6A_Law3579⟩

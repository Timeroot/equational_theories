import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 37 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `31`
equations here, 2,747 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3580 takes them (67 nodes). -/
def ordS6A_Law3580 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3580. -/
theorem noS6A_Law3580 : ∀ v : Magma.tupS6A,
    ¬ @Equation3580 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3580) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3580) (by native_decide) v.1 v.2
    ((@Law3580.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3581 takes them (44 nodes). -/
def ordS6A_Law3581 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3581. -/
theorem noS6A_Law3581 : ∀ v : Magma.tupS6A,
    ¬ @Equation3581 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3581) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3581) (by native_decide) v.1 v.2
    ((@Law3581.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3582 takes them (113 nodes). -/
def ordS6A_Law3582 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3582. -/
theorem noS6A_Law3582 : ∀ v : Magma.tupS6A,
    ¬ @Equation3582 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3582) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3582) (by native_decide) v.1 v.2
    ((@Law3582.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3584 takes them (108 nodes). -/
def ordS6A_Law3584 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3584. -/
theorem noS6A_Law3584 : ∀ v : Magma.tupS6A,
    ¬ @Equation3584 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3584) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3584) (by native_decide) v.1 v.2
    ((@Law3584.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3585 takes them (107 nodes). -/
def ordS6A_Law3585 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3585. -/
theorem noS6A_Law3585 : ∀ v : Magma.tupS6A,
    ¬ @Equation3585 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3585) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3585) (by native_decide) v.1 v.2
    ((@Law3585.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3586 takes them (84 nodes). -/
def ordS6A_Law3586 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3586. -/
theorem noS6A_Law3586 : ∀ v : Magma.tupS6A,
    ¬ @Equation3586 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3586) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3586) (by native_decide) v.1 v.2
    ((@Law3586.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3589 takes them (48 nodes). -/
def ordS6A_Law3589 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3589. -/
theorem noS6A_Law3589 : ∀ v : Magma.tupS6A,
    ¬ @Equation3589 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3589) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3589) (by native_decide) v.1 v.2
    ((@Law3589.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3590 takes them (57 nodes). -/
def ordS6A_Law3590 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3590. -/
theorem noS6A_Law3590 : ∀ v : Magma.tupS6A,
    ¬ @Equation3590 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3590) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3590) (by native_decide) v.1 v.2
    ((@Law3590.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3591 takes them (130 nodes). -/
def ordS6A_Law3591 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3591. -/
theorem noS6A_Law3591 : ∀ v : Magma.tupS6A,
    ¬ @Equation3591 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3591) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3591) (by native_decide) v.1 v.2
    ((@Law3591.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3592 takes them (55 nodes). -/
def ordS6A_Law3592 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3592. -/
theorem noS6A_Law3592 : ∀ v : Magma.tupS6A,
    ¬ @Equation3592 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3592) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3592) (by native_decide) v.1 v.2
    ((@Law3592.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3593 takes them (55 nodes). -/
def ordS6A_Law3593 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3593. -/
theorem noS6A_Law3593 : ∀ v : Magma.tupS6A,
    ¬ @Equation3593 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3593) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3593) (by native_decide) v.1 v.2
    ((@Law3593.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3594 takes them (26 nodes). -/
def ordS6A_Law3594 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3594. -/
theorem noS6A_Law3594 : ∀ v : Magma.tupS6A,
    ¬ @Equation3594 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3594) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3594) (by native_decide) v.1 v.2
    ((@Law3594.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3595 takes them (51 nodes). -/
def ordS6A_Law3595 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3595. -/
theorem noS6A_Law3595 : ∀ v : Magma.tupS6A,
    ¬ @Equation3595 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3595) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3595) (by native_decide) v.1 v.2
    ((@Law3595.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3596 takes them (24 nodes). -/
def ordS6A_Law3596 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3596. -/
theorem noS6A_Law3596 : ∀ v : Magma.tupS6A,
    ¬ @Equation3596 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3596) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3596) (by native_decide) v.1 v.2
    ((@Law3596.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3597 takes them (24 nodes). -/
def ordS6A_Law3597 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3597. -/
theorem noS6A_Law3597 : ∀ v : Magma.tupS6A,
    ¬ @Equation3597 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3597) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3597) (by native_decide) v.1 v.2
    ((@Law3597.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3598 takes them (24 nodes). -/
def ordS6A_Law3598 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3598. -/
theorem noS6A_Law3598 : ∀ v : Magma.tupS6A,
    ¬ @Equation3598 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3598) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3598) (by native_decide) v.1 v.2
    ((@Law3598.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3599 takes them (152 nodes). -/
def ordS6A_Law3599 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3599. -/
theorem noS6A_Law3599 : ∀ v : Magma.tupS6A,
    ¬ @Equation3599 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3599) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3599) (by native_decide) v.1 v.2
    ((@Law3599.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3602 takes them (106 nodes). -/
def ordS6A_Law3602 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3602. -/
theorem noS6A_Law3602 : ∀ v : Magma.tupS6A,
    ¬ @Equation3602 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3602) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3602) (by native_decide) v.1 v.2
    ((@Law3602.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3603 takes them (138 nodes). -/
def ordS6A_Law3603 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3603. -/
theorem noS6A_Law3603 : ∀ v : Magma.tupS6A,
    ¬ @Equation3603 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3603) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3603) (by native_decide) v.1 v.2
    ((@Law3603.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3604 takes them (287 nodes). -/
def ordS6A_Law3604 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3604. -/
theorem noS6A_Law3604 : ∀ v : Magma.tupS6A,
    ¬ @Equation3604 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3604) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3604) (by native_decide) v.1 v.2
    ((@Law3604.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3605 takes them (159 nodes). -/
def ordS6A_Law3605 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3605. -/
theorem noS6A_Law3605 : ∀ v : Magma.tupS6A,
    ¬ @Equation3605 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3605) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3605) (by native_decide) v.1 v.2
    ((@Law3605.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3606 takes them (122 nodes). -/
def ordS6A_Law3606 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3606. -/
theorem noS6A_Law3606 : ∀ v : Magma.tupS6A,
    ¬ @Equation3606 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3606) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3606) (by native_decide) v.1 v.2
    ((@Law3606.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3607 takes them (150 nodes). -/
def ordS6A_Law3607 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3607. -/
theorem noS6A_Law3607 : ∀ v : Magma.tupS6A,
    ¬ @Equation3607 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3607) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3607) (by native_decide) v.1 v.2
    ((@Law3607.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3608 takes them (139 nodes). -/
def ordS6A_Law3608 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3608. -/
theorem noS6A_Law3608 : ∀ v : Magma.tupS6A,
    ¬ @Equation3608 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3608) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3608) (by native_decide) v.1 v.2
    ((@Law3608.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3609 takes them (83 nodes). -/
def ordS6A_Law3609 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3609. -/
theorem noS6A_Law3609 : ∀ v : Magma.tupS6A,
    ¬ @Equation3609 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3609) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3609) (by native_decide) v.1 v.2
    ((@Law3609.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3610 takes them (70 nodes). -/
def ordS6A_Law3610 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3610. -/
theorem noS6A_Law3610 : ∀ v : Magma.tupS6A,
    ¬ @Equation3610 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3610) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3610) (by native_decide) v.1 v.2
    ((@Law3610.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3611 takes them (55 nodes). -/
def ordS6A_Law3611 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3611. -/
theorem noS6A_Law3611 : ∀ v : Magma.tupS6A,
    ¬ @Equation3611 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3611) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3611) (by native_decide) v.1 v.2
    ((@Law3611.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3612 takes them (111 nodes). -/
def ordS6A_Law3612 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3612. -/
theorem noS6A_Law3612 : ∀ v : Magma.tupS6A,
    ¬ @Equation3612 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3612) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3612) (by native_decide) v.1 v.2
    ((@Law3612.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3613 takes them (55 nodes). -/
def ordS6A_Law3613 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3613. -/
theorem noS6A_Law3613 : ∀ v : Magma.tupS6A,
    ¬ @Equation3613 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3613) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3613) (by native_decide) v.1 v.2
    ((@Law3613.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3614 takes them (61 nodes). -/
def ordS6A_Law3614 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3614. -/
theorem noS6A_Law3614 : ∀ v : Magma.tupS6A,
    ¬ @Equation3614 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3614) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3614) (by native_decide) v.1 v.2
    ((@Law3614.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3615 takes them (42 nodes). -/
def ordS6A_Law3615 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3615. -/
theorem noS6A_Law3615 : ∀ v : Magma.tupS6A,
    ¬ @Equation3615 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3615) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3615) (by native_decide) v.1 v.2
    ((@Law3615.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `31` equations. -/
theorem srch6A_refutes_36 :
    FamilyRefutes Magma.srch6A [
      3580, 3581, 3582, 3584, 3585, 3586, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597,
      3598, 3599, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614,
      3615
    ] :=
  ⟨noS6A_Law3580, noS6A_Law3581, noS6A_Law3582, noS6A_Law3584, noS6A_Law3585, noS6A_Law3586, noS6A_Law3589, noS6A_Law3590, noS6A_Law3591, noS6A_Law3592, noS6A_Law3593, noS6A_Law3594, noS6A_Law3595, noS6A_Law3596, noS6A_Law3597, noS6A_Law3598, noS6A_Law3599, noS6A_Law3602, noS6A_Law3603, noS6A_Law3604, noS6A_Law3605, noS6A_Law3606, noS6A_Law3607, noS6A_Law3608, noS6A_Law3609, noS6A_Law3610, noS6A_Law3611, noS6A_Law3612, noS6A_Law3613, noS6A_Law3614, noS6A_Law3615⟩

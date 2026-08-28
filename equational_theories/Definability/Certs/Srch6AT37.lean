import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 38 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `38`
equations here, 2,478 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3616 takes them (56 nodes). -/
def ordS6A_Law3616 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3616. -/
theorem noS6A_Law3616 : ∀ v : Magma.tupS6A,
    ¬ @Equation3616 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3616) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3616) (by native_decide) v.1 v.2
    ((@Law3616.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3617 takes them (176 nodes). -/
def ordS6A_Law3617 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3617. -/
theorem noS6A_Law3617 : ∀ v : Magma.tupS6A,
    ¬ @Equation3617 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3617) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3617) (by native_decide) v.1 v.2
    ((@Law3617.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3618 takes them (55 nodes). -/
def ordS6A_Law3618 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3618. -/
theorem noS6A_Law3618 : ∀ v : Magma.tupS6A,
    ¬ @Equation3618 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3618) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3618) (by native_decide) v.1 v.2
    ((@Law3618.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3619 takes them (55 nodes). -/
def ordS6A_Law3619 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3619. -/
theorem noS6A_Law3619 : ∀ v : Magma.tupS6A,
    ¬ @Equation3619 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3619) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3619) (by native_decide) v.1 v.2
    ((@Law3619.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3620 takes them (76 nodes). -/
def ordS6A_Law3620 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3620. -/
theorem noS6A_Law3620 : ∀ v : Magma.tupS6A,
    ¬ @Equation3620 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3620) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3620) (by native_decide) v.1 v.2
    ((@Law3620.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3621 takes them (75 nodes). -/
def ordS6A_Law3621 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3621. -/
theorem noS6A_Law3621 : ∀ v : Magma.tupS6A,
    ¬ @Equation3621 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3621) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3621) (by native_decide) v.1 v.2
    ((@Law3621.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3622 takes them (32 nodes). -/
def ordS6A_Law3622 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3622. -/
theorem noS6A_Law3622 : ∀ v : Magma.tupS6A,
    ¬ @Equation3622 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3622) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3622) (by native_decide) v.1 v.2
    ((@Law3622.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3623 takes them (27 nodes). -/
def ordS6A_Law3623 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3623. -/
theorem noS6A_Law3623 : ∀ v : Magma.tupS6A,
    ¬ @Equation3623 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3623) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3623) (by native_decide) v.1 v.2
    ((@Law3623.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3624 takes them (98 nodes). -/
def ordS6A_Law3624 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3624. -/
theorem noS6A_Law3624 : ∀ v : Magma.tupS6A,
    ¬ @Equation3624 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3624) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3624) (by native_decide) v.1 v.2
    ((@Law3624.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3625 takes them (129 nodes). -/
def ordS6A_Law3625 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3625. -/
theorem noS6A_Law3625 : ∀ v : Magma.tupS6A,
    ¬ @Equation3625 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3625) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3625) (by native_decide) v.1 v.2
    ((@Law3625.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3626 takes them (95 nodes). -/
def ordS6A_Law3626 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3626. -/
theorem noS6A_Law3626 : ∀ v : Magma.tupS6A,
    ¬ @Equation3626 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3626) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3626) (by native_decide) v.1 v.2
    ((@Law3626.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3627 takes them (95 nodes). -/
def ordS6A_Law3627 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3627. -/
theorem noS6A_Law3627 : ∀ v : Magma.tupS6A,
    ¬ @Equation3627 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3627) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3627) (by native_decide) v.1 v.2
    ((@Law3627.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3628 takes them (25 nodes). -/
def ordS6A_Law3628 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3628. -/
theorem noS6A_Law3628 : ∀ v : Magma.tupS6A,
    ¬ @Equation3628 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3628) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3628) (by native_decide) v.1 v.2
    ((@Law3628.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3629 takes them (50 nodes). -/
def ordS6A_Law3629 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3629. -/
theorem noS6A_Law3629 : ∀ v : Magma.tupS6A,
    ¬ @Equation3629 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3629) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3629) (by native_decide) v.1 v.2
    ((@Law3629.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3630 takes them (22 nodes). -/
def ordS6A_Law3630 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3630. -/
theorem noS6A_Law3630 : ∀ v : Magma.tupS6A,
    ¬ @Equation3630 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3630) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3630) (by native_decide) v.1 v.2
    ((@Law3630.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3631 takes them (22 nodes). -/
def ordS6A_Law3631 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3631. -/
theorem noS6A_Law3631 : ∀ v : Magma.tupS6A,
    ¬ @Equation3631 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3631) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3631) (by native_decide) v.1 v.2
    ((@Law3631.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3632 takes them (22 nodes). -/
def ordS6A_Law3632 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3632. -/
theorem noS6A_Law3632 : ∀ v : Magma.tupS6A,
    ¬ @Equation3632 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3632) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3632) (by native_decide) v.1 v.2
    ((@Law3632.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3633 takes them (55 nodes). -/
def ordS6A_Law3633 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3633. -/
theorem noS6A_Law3633 : ∀ v : Magma.tupS6A,
    ¬ @Equation3633 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3633) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3633) (by native_decide) v.1 v.2
    ((@Law3633.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3634 takes them (115 nodes). -/
def ordS6A_Law3634 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3634. -/
theorem noS6A_Law3634 : ∀ v : Magma.tupS6A,
    ¬ @Equation3634 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3634) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3634) (by native_decide) v.1 v.2
    ((@Law3634.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3635 takes them (55 nodes). -/
def ordS6A_Law3635 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3635. -/
theorem noS6A_Law3635 : ∀ v : Magma.tupS6A,
    ¬ @Equation3635 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3635) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3635) (by native_decide) v.1 v.2
    ((@Law3635.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3636 takes them (55 nodes). -/
def ordS6A_Law3636 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3636. -/
theorem noS6A_Law3636 : ∀ v : Magma.tupS6A,
    ¬ @Equation3636 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3636) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3636) (by native_decide) v.1 v.2
    ((@Law3636.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3637 takes them (55 nodes). -/
def ordS6A_Law3637 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3637. -/
theorem noS6A_Law3637 : ∀ v : Magma.tupS6A,
    ¬ @Equation3637 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3637) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3637) (by native_decide) v.1 v.2
    ((@Law3637.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3638 takes them (33 nodes). -/
def ordS6A_Law3638 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3638. -/
theorem noS6A_Law3638 : ∀ v : Magma.tupS6A,
    ¬ @Equation3638 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3638) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3638) (by native_decide) v.1 v.2
    ((@Law3638.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3639 takes them (73 nodes). -/
def ordS6A_Law3639 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3639. -/
theorem noS6A_Law3639 : ∀ v : Magma.tupS6A,
    ¬ @Equation3639 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3639) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3639) (by native_decide) v.1 v.2
    ((@Law3639.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3640 takes them (32 nodes). -/
def ordS6A_Law3640 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3640. -/
theorem noS6A_Law3640 : ∀ v : Magma.tupS6A,
    ¬ @Equation3640 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3640) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3640) (by native_decide) v.1 v.2
    ((@Law3640.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3641 takes them (32 nodes). -/
def ordS6A_Law3641 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3641. -/
theorem noS6A_Law3641 : ∀ v : Magma.tupS6A,
    ¬ @Equation3641 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3641) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3641) (by native_decide) v.1 v.2
    ((@Law3641.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3642 takes them (27 nodes). -/
def ordS6A_Law3642 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3642. -/
theorem noS6A_Law3642 : ∀ v : Magma.tupS6A,
    ¬ @Equation3642 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3642) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3642) (by native_decide) v.1 v.2
    ((@Law3642.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3643 takes them (55 nodes). -/
def ordS6A_Law3643 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3643. -/
theorem noS6A_Law3643 : ∀ v : Magma.tupS6A,
    ¬ @Equation3643 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3643) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3643) (by native_decide) v.1 v.2
    ((@Law3643.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3644 takes them (87 nodes). -/
def ordS6A_Law3644 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3644. -/
theorem noS6A_Law3644 : ∀ v : Magma.tupS6A,
    ¬ @Equation3644 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3644) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3644) (by native_decide) v.1 v.2
    ((@Law3644.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3645 takes them (53 nodes). -/
def ordS6A_Law3645 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3645. -/
theorem noS6A_Law3645 : ∀ v : Magma.tupS6A,
    ¬ @Equation3645 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3645) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3645) (by native_decide) v.1 v.2
    ((@Law3645.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3646 takes them (53 nodes). -/
def ordS6A_Law3646 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3646. -/
theorem noS6A_Law3646 : ∀ v : Magma.tupS6A,
    ¬ @Equation3646 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3646) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3646) (by native_decide) v.1 v.2
    ((@Law3646.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3647 takes them (53 nodes). -/
def ordS6A_Law3647 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3647. -/
theorem noS6A_Law3647 : ∀ v : Magma.tupS6A,
    ¬ @Equation3647 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3647) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3647) (by native_decide) v.1 v.2
    ((@Law3647.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3648 takes them (97 nodes). -/
def ordS6A_Law3648 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3648. -/
theorem noS6A_Law3648 : ∀ v : Magma.tupS6A,
    ¬ @Equation3648 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3648) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3648) (by native_decide) v.1 v.2
    ((@Law3648.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3649 takes them (129 nodes). -/
def ordS6A_Law3649 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3649. -/
theorem noS6A_Law3649 : ∀ v : Magma.tupS6A,
    ¬ @Equation3649 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3649) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3649) (by native_decide) v.1 v.2
    ((@Law3649.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3650 takes them (95 nodes). -/
def ordS6A_Law3650 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3650. -/
theorem noS6A_Law3650 : ∀ v : Magma.tupS6A,
    ¬ @Equation3650 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3650) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3650) (by native_decide) v.1 v.2
    ((@Law3650.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3651 takes them (95 nodes). -/
def ordS6A_Law3651 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3651. -/
theorem noS6A_Law3651 : ∀ v : Magma.tupS6A,
    ¬ @Equation3651 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3651) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3651) (by native_decide) v.1 v.2
    ((@Law3651.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3652 takes them (95 nodes). -/
def ordS6A_Law3652 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3652. -/
theorem noS6A_Law3652 : ∀ v : Magma.tupS6A,
    ¬ @Equation3652 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3652) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3652) (by native_decide) v.1 v.2
    ((@Law3652.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3653 takes them (24 nodes). -/
def ordS6A_Law3653 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3653. -/
theorem noS6A_Law3653 : ∀ v : Magma.tupS6A,
    ¬ @Equation3653 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3653) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3653) (by native_decide) v.1 v.2
    ((@Law3653.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `38` equations. -/
theorem srch6A_refutes_37 :
    FamilyRefutes Magma.srch6A [
      3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630,
      3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645,
      3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653
    ] :=
  ⟨noS6A_Law3616, noS6A_Law3617, noS6A_Law3618, noS6A_Law3619, noS6A_Law3620, noS6A_Law3621, noS6A_Law3622, noS6A_Law3623, noS6A_Law3624, noS6A_Law3625, noS6A_Law3626, noS6A_Law3627, noS6A_Law3628, noS6A_Law3629, noS6A_Law3630, noS6A_Law3631, noS6A_Law3632, noS6A_Law3633, noS6A_Law3634, noS6A_Law3635, noS6A_Law3636, noS6A_Law3637, noS6A_Law3638, noS6A_Law3639, noS6A_Law3640, noS6A_Law3641, noS6A_Law3642, noS6A_Law3643, noS6A_Law3644, noS6A_Law3645, noS6A_Law3646, noS6A_Law3647, noS6A_Law3648, noS6A_Law3649, noS6A_Law3650, noS6A_Law3651, noS6A_Law3652, noS6A_Law3653⟩

import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 8 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `82` equations here, 694 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3634 takes them (10 nodes). -/
def ordS8R164_Law3634 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3634. -/
theorem noS8R164_Law3634 : ∀ v : Magma.tup8R164,
    ¬ @Equation3634 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3634) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3634) (by native_decide) v.1 v.2
    ((@Law3634.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3635 takes them (6 nodes). -/
def ordS8R164_Law3635 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3635. -/
theorem noS8R164_Law3635 : ∀ v : Magma.tup8R164,
    ¬ @Equation3635 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3635) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3635) (by native_decide) v.1 v.2
    ((@Law3635.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3636 takes them (6 nodes). -/
def ordS8R164_Law3636 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3636. -/
theorem noS8R164_Law3636 : ∀ v : Magma.tup8R164,
    ¬ @Equation3636 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3636) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3636) (by native_decide) v.1 v.2
    ((@Law3636.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3637 takes them (6 nodes). -/
def ordS8R164_Law3637 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3637. -/
theorem noS8R164_Law3637 : ∀ v : Magma.tup8R164,
    ¬ @Equation3637 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3637) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3637) (by native_decide) v.1 v.2
    ((@Law3637.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3638 takes them (7 nodes). -/
def ordS8R164_Law3638 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3638. -/
theorem noS8R164_Law3638 : ∀ v : Magma.tup8R164,
    ¬ @Equation3638 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3638) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3638) (by native_decide) v.1 v.2
    ((@Law3638.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3639 takes them (10 nodes). -/
def ordS8R164_Law3639 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3639. -/
theorem noS8R164_Law3639 : ∀ v : Magma.tup8R164,
    ¬ @Equation3639 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3639) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3639) (by native_decide) v.1 v.2
    ((@Law3639.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3640 takes them (7 nodes). -/
def ordS8R164_Law3640 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3640. -/
theorem noS8R164_Law3640 : ∀ v : Magma.tup8R164,
    ¬ @Equation3640 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3640) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3640) (by native_decide) v.1 v.2
    ((@Law3640.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3641 takes them (7 nodes). -/
def ordS8R164_Law3641 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3641. -/
theorem noS8R164_Law3641 : ∀ v : Magma.tup8R164,
    ¬ @Equation3641 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3641) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3641) (by native_decide) v.1 v.2
    ((@Law3641.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3642 takes them (6 nodes). -/
def ordS8R164_Law3642 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3642. -/
theorem noS8R164_Law3642 : ∀ v : Magma.tup8R164,
    ¬ @Equation3642 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3642) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3642) (by native_decide) v.1 v.2
    ((@Law3642.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3643 takes them (6 nodes). -/
def ordS8R164_Law3643 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3643. -/
theorem noS8R164_Law3643 : ∀ v : Magma.tup8R164,
    ¬ @Equation3643 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3643) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3643) (by native_decide) v.1 v.2
    ((@Law3643.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3644 takes them (10 nodes). -/
def ordS8R164_Law3644 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3644. -/
theorem noS8R164_Law3644 : ∀ v : Magma.tup8R164,
    ¬ @Equation3644 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3644) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3644) (by native_decide) v.1 v.2
    ((@Law3644.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3645 takes them (6 nodes). -/
def ordS8R164_Law3645 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3645. -/
theorem noS8R164_Law3645 : ∀ v : Magma.tup8R164,
    ¬ @Equation3645 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3645) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3645) (by native_decide) v.1 v.2
    ((@Law3645.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3646 takes them (6 nodes). -/
def ordS8R164_Law3646 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3646. -/
theorem noS8R164_Law3646 : ∀ v : Magma.tup8R164,
    ¬ @Equation3646 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3646) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3646) (by native_decide) v.1 v.2
    ((@Law3646.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3647 takes them (6 nodes). -/
def ordS8R164_Law3647 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3647. -/
theorem noS8R164_Law3647 : ∀ v : Magma.tup8R164,
    ¬ @Equation3647 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3647) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3647) (by native_decide) v.1 v.2
    ((@Law3647.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3648 takes them (6 nodes). -/
def ordS8R164_Law3648 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3648. -/
theorem noS8R164_Law3648 : ∀ v : Magma.tup8R164,
    ¬ @Equation3648 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3648) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3648) (by native_decide) v.1 v.2
    ((@Law3648.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3649 takes them (10 nodes). -/
def ordS8R164_Law3649 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3649. -/
theorem noS8R164_Law3649 : ∀ v : Magma.tup8R164,
    ¬ @Equation3649 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3649) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3649) (by native_decide) v.1 v.2
    ((@Law3649.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3650 takes them (6 nodes). -/
def ordS8R164_Law3650 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3650. -/
theorem noS8R164_Law3650 : ∀ v : Magma.tup8R164,
    ¬ @Equation3650 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3650) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3650) (by native_decide) v.1 v.2
    ((@Law3650.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3651 takes them (6 nodes). -/
def ordS8R164_Law3651 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3651. -/
theorem noS8R164_Law3651 : ∀ v : Magma.tup8R164,
    ¬ @Equation3651 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3651) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3651) (by native_decide) v.1 v.2
    ((@Law3651.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3652 takes them (6 nodes). -/
def ordS8R164_Law3652 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3652. -/
theorem noS8R164_Law3652 : ∀ v : Magma.tup8R164,
    ¬ @Equation3652 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3652) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3652) (by native_decide) v.1 v.2
    ((@Law3652.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3653 takes them (6 nodes). -/
def ordS8R164_Law3653 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3653. -/
theorem noS8R164_Law3653 : ∀ v : Magma.tup8R164,
    ¬ @Equation3653 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3653) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3653) (by native_decide) v.1 v.2
    ((@Law3653.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3654 takes them (10 nodes). -/
def ordS8R164_Law3654 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3654. -/
theorem noS8R164_Law3654 : ∀ v : Magma.tup8R164,
    ¬ @Equation3654 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3654) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3654) (by native_decide) v.1 v.2
    ((@Law3654.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3655 takes them (6 nodes). -/
def ordS8R164_Law3655 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3655. -/
theorem noS8R164_Law3655 : ∀ v : Magma.tup8R164,
    ¬ @Equation3655 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3655) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3655) (by native_decide) v.1 v.2
    ((@Law3655.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3656 takes them (6 nodes). -/
def ordS8R164_Law3656 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3656. -/
theorem noS8R164_Law3656 : ∀ v : Magma.tup8R164,
    ¬ @Equation3656 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3656) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3656) (by native_decide) v.1 v.2
    ((@Law3656.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3657 takes them (6 nodes). -/
def ordS8R164_Law3657 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3657. -/
theorem noS8R164_Law3657 : ∀ v : Magma.tup8R164,
    ¬ @Equation3657 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3657) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3657) (by native_decide) v.1 v.2
    ((@Law3657.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3658 takes them (6 nodes). -/
def ordS8R164_Law3658 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3658. -/
theorem noS8R164_Law3658 : ∀ v : Magma.tup8R164,
    ¬ @Equation3658 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3658) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law3658) (by native_decide) v.1 v.2
    ((@Law3658.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3666 takes them (10 nodes). -/
def ordS8R164_Law3666 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3666. -/
theorem noS8R164_Law3666 : ∀ v : Magma.tup8R164,
    ¬ @Equation3666 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3666) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3666) (by native_decide) v.1 v.2
    ((@Law3666.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3669 takes them (9 nodes). -/
def ordS8R164_Law3669 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3669. -/
theorem noS8R164_Law3669 : ∀ v : Magma.tup8R164,
    ¬ @Equation3669 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3669) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3669) (by native_decide) v.1 v.2
    ((@Law3669.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3670 takes them (13 nodes). -/
def ordS8R164_Law3670 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3670. -/
theorem noS8R164_Law3670 : ∀ v : Magma.tup8R164,
    ¬ @Equation3670 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3670) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3670) (by native_decide) v.1 v.2
    ((@Law3670.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3671 takes them (12 nodes). -/
def ordS8R164_Law3671 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3671. -/
theorem noS8R164_Law3671 : ∀ v : Magma.tup8R164,
    ¬ @Equation3671 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3671) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3671) (by native_decide) v.1 v.2
    ((@Law3671.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3673 takes them (9 nodes). -/
def ordS8R164_Law3673 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3673. -/
theorem noS8R164_Law3673 : ∀ v : Magma.tup8R164,
    ¬ @Equation3673 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3673) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3673) (by native_decide) v.1 v.2
    ((@Law3673.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3676 takes them (6 nodes). -/
def ordS8R164_Law3676 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3676. -/
theorem noS8R164_Law3676 : ∀ v : Magma.tup8R164,
    ¬ @Equation3676 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3676) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3676) (by native_decide) v.1 v.2
    ((@Law3676.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3679 takes them (8 nodes). -/
def ordS8R164_Law3679 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3679. -/
theorem noS8R164_Law3679 : ∀ v : Magma.tup8R164,
    ¬ @Equation3679 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3679) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3679) (by native_decide) v.1 v.2
    ((@Law3679.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3680 takes them (11 nodes). -/
def ordS8R164_Law3680 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3680. -/
theorem noS8R164_Law3680 : ∀ v : Magma.tup8R164,
    ¬ @Equation3680 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3680) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3680) (by native_decide) v.1 v.2
    ((@Law3680.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3681 takes them (7 nodes). -/
def ordS8R164_Law3681 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3681. -/
theorem noS8R164_Law3681 : ∀ v : Magma.tup8R164,
    ¬ @Equation3681 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3681) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3681) (by native_decide) v.1 v.2
    ((@Law3681.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3683 takes them (6 nodes). -/
def ordS8R164_Law3683 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3683. -/
theorem noS8R164_Law3683 : ∀ v : Magma.tup8R164,
    ¬ @Equation3683 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3683) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3683) (by native_decide) v.1 v.2
    ((@Law3683.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3695 takes them (7 nodes). -/
def ordS8R164_Law3695 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3695. -/
theorem noS8R164_Law3695 : ∀ v : Magma.tup8R164,
    ¬ @Equation3695 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3695) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3695) (by native_decide) v.1 v.2
    ((@Law3695.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3696 takes them (9 nodes). -/
def ordS8R164_Law3696 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3696. -/
theorem noS8R164_Law3696 : ∀ v : Magma.tup8R164,
    ¬ @Equation3696 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3696) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3696) (by native_decide) v.1 v.2
    ((@Law3696.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3697 takes them (6 nodes). -/
def ordS8R164_Law3697 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3697. -/
theorem noS8R164_Law3697 : ∀ v : Magma.tup8R164,
    ¬ @Equation3697 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3697) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3697) (by native_decide) v.1 v.2
    ((@Law3697.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3698 takes them (12 nodes). -/
def ordS8R164_Law3698 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3698. -/
theorem noS8R164_Law3698 : ∀ v : Magma.tup8R164,
    ¬ @Equation3698 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3698) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3698) (by native_decide) v.1 v.2
    ((@Law3698.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3701 takes them (8 nodes). -/
def ordS8R164_Law3701 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3701. -/
theorem noS8R164_Law3701 : ∀ v : Magma.tup8R164,
    ¬ @Equation3701 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3701) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3701) (by native_decide) v.1 v.2
    ((@Law3701.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3702 takes them (10 nodes). -/
def ordS8R164_Law3702 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3702. -/
theorem noS8R164_Law3702 : ∀ v : Magma.tup8R164,
    ¬ @Equation3702 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3702) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3702) (by native_decide) v.1 v.2
    ((@Law3702.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3705 takes them (6 nodes). -/
def ordS8R164_Law3705 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3705. -/
theorem noS8R164_Law3705 : ∀ v : Magma.tup8R164,
    ¬ @Equation3705 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3705) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3705) (by native_decide) v.1 v.2
    ((@Law3705.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3706 takes them (10 nodes). -/
def ordS8R164_Law3706 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3706. -/
theorem noS8R164_Law3706 : ∀ v : Magma.tup8R164,
    ¬ @Equation3706 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3706) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3706) (by native_decide) v.1 v.2
    ((@Law3706.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3707 takes them (7 nodes). -/
def ordS8R164_Law3707 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3707. -/
theorem noS8R164_Law3707 : ∀ v : Magma.tup8R164,
    ¬ @Equation3707 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3707) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3707) (by native_decide) v.1 v.2
    ((@Law3707.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3708 takes them (9 nodes). -/
def ordS8R164_Law3708 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3708. -/
theorem noS8R164_Law3708 : ∀ v : Magma.tup8R164,
    ¬ @Equation3708 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3708) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3708) (by native_decide) v.1 v.2
    ((@Law3708.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3710 takes them (6 nodes). -/
def ordS8R164_Law3710 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3710. -/
theorem noS8R164_Law3710 : ∀ v : Magma.tup8R164,
    ¬ @Equation3710 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3710) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3710) (by native_decide) v.1 v.2
    ((@Law3710.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3711 takes them (9 nodes). -/
def ordS8R164_Law3711 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3711. -/
theorem noS8R164_Law3711 : ∀ v : Magma.tup8R164,
    ¬ @Equation3711 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3711) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3711) (by native_decide) v.1 v.2
    ((@Law3711.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3713 takes them (9 nodes). -/
def ordS8R164_Law3713 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3713. -/
theorem noS8R164_Law3713 : ∀ v : Magma.tup8R164,
    ¬ @Equation3713 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3713) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3713) (by native_decide) v.1 v.2
    ((@Law3713.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3716 takes them (9 nodes). -/
def ordS8R164_Law3716 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3716. -/
theorem noS8R164_Law3716 : ∀ v : Magma.tup8R164,
    ¬ @Equation3716 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3716) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3716) (by native_decide) v.1 v.2
    ((@Law3716.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3717 takes them (9 nodes). -/
def ordS8R164_Law3717 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3717. -/
theorem noS8R164_Law3717 : ∀ v : Magma.tup8R164,
    ¬ @Equation3717 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3717) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3717) (by native_decide) v.1 v.2
    ((@Law3717.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3718 takes them (13 nodes). -/
def ordS8R164_Law3718 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3718. -/
theorem noS8R164_Law3718 : ∀ v : Magma.tup8R164,
    ¬ @Equation3718 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3718) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3718) (by native_decide) v.1 v.2
    ((@Law3718.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3719 takes them (9 nodes). -/
def ordS8R164_Law3719 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3719. -/
theorem noS8R164_Law3719 : ∀ v : Magma.tup8R164,
    ¬ @Equation3719 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3719) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3719) (by native_decide) v.1 v.2
    ((@Law3719.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3720 takes them (9 nodes). -/
def ordS8R164_Law3720 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3720. -/
theorem noS8R164_Law3720 : ∀ v : Magma.tup8R164,
    ¬ @Equation3720 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3720) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3720) (by native_decide) v.1 v.2
    ((@Law3720.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3723 takes them (10 nodes). -/
def ordS8R164_Law3723 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3723. -/
theorem noS8R164_Law3723 : ∀ v : Magma.tup8R164,
    ¬ @Equation3723 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3723) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3723) (by native_decide) v.1 v.2
    ((@Law3723.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3726 takes them (13 nodes). -/
def ordS8R164_Law3726 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3726. -/
theorem noS8R164_Law3726 : ∀ v : Magma.tup8R164,
    ¬ @Equation3726 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3726) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3726) (by native_decide) v.1 v.2
    ((@Law3726.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3727 takes them (14 nodes). -/
def ordS8R164_Law3727 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3727. -/
theorem noS8R164_Law3727 : ∀ v : Magma.tup8R164,
    ¬ @Equation3727 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3727) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3727) (by native_decide) v.1 v.2
    ((@Law3727.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3728 takes them (14 nodes). -/
def ordS8R164_Law3728 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3728. -/
theorem noS8R164_Law3728 : ∀ v : Magma.tup8R164,
    ¬ @Equation3728 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3728) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3728) (by native_decide) v.1 v.2
    ((@Law3728.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3730 takes them (9 nodes). -/
def ordS8R164_Law3730 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3730. -/
theorem noS8R164_Law3730 : ∀ v : Magma.tup8R164,
    ¬ @Equation3730 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3730) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3730) (by native_decide) v.1 v.2
    ((@Law3730.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3731 takes them (9 nodes). -/
def ordS8R164_Law3731 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3731. -/
theorem noS8R164_Law3731 : ∀ v : Magma.tup8R164,
    ¬ @Equation3731 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3731) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3731) (by native_decide) v.1 v.2
    ((@Law3731.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3732 takes them (14 nodes). -/
def ordS8R164_Law3732 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3732. -/
theorem noS8R164_Law3732 : ∀ v : Magma.tup8R164,
    ¬ @Equation3732 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3732) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3732) (by native_decide) v.1 v.2
    ((@Law3732.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3733 takes them (9 nodes). -/
def ordS8R164_Law3733 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3733. -/
theorem noS8R164_Law3733 : ∀ v : Magma.tup8R164,
    ¬ @Equation3733 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3733) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3733) (by native_decide) v.1 v.2
    ((@Law3733.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3734 takes them (9 nodes). -/
def ordS8R164_Law3734 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3734. -/
theorem noS8R164_Law3734 : ∀ v : Magma.tup8R164,
    ¬ @Equation3734 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3734) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3734) (by native_decide) v.1 v.2
    ((@Law3734.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3735 takes them (10 nodes). -/
def ordS8R164_Law3735 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3735. -/
theorem noS8R164_Law3735 : ∀ v : Magma.tup8R164,
    ¬ @Equation3735 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3735) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3735) (by native_decide) v.1 v.2
    ((@Law3735.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3736 takes them (13 nodes). -/
def ordS8R164_Law3736 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3736. -/
theorem noS8R164_Law3736 : ∀ v : Magma.tup8R164,
    ¬ @Equation3736 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3736) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3736) (by native_decide) v.1 v.2
    ((@Law3736.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3738 takes them (9 nodes). -/
def ordS8R164_Law3738 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3738. -/
theorem noS8R164_Law3738 : ∀ v : Magma.tup8R164,
    ¬ @Equation3738 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3738) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3738) (by native_decide) v.1 v.2
    ((@Law3738.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3739 takes them (9 nodes). -/
def ordS8R164_Law3739 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3739. -/
theorem noS8R164_Law3739 : ∀ v : Magma.tup8R164,
    ¬ @Equation3739 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3739) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3739) (by native_decide) v.1 v.2
    ((@Law3739.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3741 takes them (9 nodes). -/
def ordS8R164_Law3741 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3741. -/
theorem noS8R164_Law3741 : ∀ v : Magma.tup8R164,
    ¬ @Equation3741 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3741) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3741) (by native_decide) v.1 v.2
    ((@Law3741.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3742 takes them (9 nodes). -/
def ordS8R164_Law3742 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3742. -/
theorem noS8R164_Law3742 : ∀ v : Magma.tup8R164,
    ¬ @Equation3742 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3742) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3742) (by native_decide) v.1 v.2
    ((@Law3742.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3743 takes them (9 nodes). -/
def ordS8R164_Law3743 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3743. -/
theorem noS8R164_Law3743 : ∀ v : Magma.tup8R164,
    ¬ @Equation3743 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3743) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3743) (by native_decide) v.1 v.2
    ((@Law3743.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3744 takes them (13 nodes). -/
def ordS8R164_Law3744 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3744. -/
theorem noS8R164_Law3744 : ∀ v : Magma.tup8R164,
    ¬ @Equation3744 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3744) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3744) (by native_decide) v.1 v.2
    ((@Law3744.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3745 takes them (9 nodes). -/
def ordS8R164_Law3745 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3745. -/
theorem noS8R164_Law3745 : ∀ v : Magma.tup8R164,
    ¬ @Equation3745 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3745) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3745) (by native_decide) v.1 v.2
    ((@Law3745.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3746 takes them (9 nodes). -/
def ordS8R164_Law3746 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3746. -/
theorem noS8R164_Law3746 : ∀ v : Magma.tup8R164,
    ¬ @Equation3746 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3746) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3746) (by native_decide) v.1 v.2
    ((@Law3746.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3747 takes them (9 nodes). -/
def ordS8R164_Law3747 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3747. -/
theorem noS8R164_Law3747 : ∀ v : Magma.tup8R164,
    ¬ @Equation3747 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3747) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3747) (by native_decide) v.1 v.2
    ((@Law3747.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3750 takes them (6 nodes). -/
def ordS8R164_Law3750 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3750. -/
theorem noS8R164_Law3750 : ∀ v : Magma.tup8R164,
    ¬ @Equation3750 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3750) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3750) (by native_decide) v.1 v.2
    ((@Law3750.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3753 takes them (6 nodes). -/
def ordS8R164_Law3753 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3753. -/
theorem noS8R164_Law3753 : ∀ v : Magma.tup8R164,
    ¬ @Equation3753 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3753) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3753) (by native_decide) v.1 v.2
    ((@Law3753.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3754 takes them (7 nodes). -/
def ordS8R164_Law3754 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3754. -/
theorem noS8R164_Law3754 : ∀ v : Magma.tup8R164,
    ¬ @Equation3754 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3754) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3754) (by native_decide) v.1 v.2
    ((@Law3754.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3755 takes them (10 nodes). -/
def ordS8R164_Law3755 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3755. -/
theorem noS8R164_Law3755 : ∀ v : Magma.tup8R164,
    ¬ @Equation3755 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3755) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3755) (by native_decide) v.1 v.2
    ((@Law3755.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3757 takes them (6 nodes). -/
def ordS8R164_Law3757 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3757. -/
theorem noS8R164_Law3757 : ∀ v : Magma.tup8R164,
    ¬ @Equation3757 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3757) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3757) (by native_decide) v.1 v.2
    ((@Law3757.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3760 takes them (6 nodes). -/
def ordS8R164_Law3760 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3760. -/
theorem noS8R164_Law3760 : ∀ v : Magma.tup8R164,
    ¬ @Equation3760 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3760) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3760) (by native_decide) v.1 v.2
    ((@Law3760.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3762 takes them (10 nodes). -/
def ordS8R164_Law3762 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3762. -/
theorem noS8R164_Law3762 : ∀ v : Magma.tup8R164,
    ¬ @Equation3762 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3762) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3762) (by native_decide) v.1 v.2
    ((@Law3762.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3763 takes them (6 nodes). -/
def ordS8R164_Law3763 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3763. -/
theorem noS8R164_Law3763 : ∀ v : Magma.tup8R164,
    ¬ @Equation3763 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3763) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3763) (by native_decide) v.1 v.2
    ((@Law3763.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3764 takes them (7 nodes). -/
def ordS8R164_Law3764 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3764. -/
theorem noS8R164_Law3764 : ∀ v : Magma.tup8R164,
    ¬ @Equation3764 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3764) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3764) (by native_decide) v.1 v.2
    ((@Law3764.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `82` equations. -/
theorem srch8R164_refutes_7 :
    FamilyRefutes Magma.srch8R164 [
      3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648,
      3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3666, 3669, 3670, 3671, 3673,
      3676, 3679, 3680, 3681, 3683, 3695, 3696, 3697, 3698, 3701, 3702, 3705, 3706, 3707, 3708,
      3710, 3711, 3713, 3716, 3717, 3718, 3719, 3720, 3723, 3726, 3727, 3728, 3730, 3731, 3732,
      3733, 3734, 3735, 3736, 3738, 3739, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3750, 3753,
      3754, 3755, 3757, 3760, 3762, 3763, 3764
    ] :=
  ⟨noS8R164_Law3634, noS8R164_Law3635, noS8R164_Law3636, noS8R164_Law3637, noS8R164_Law3638, noS8R164_Law3639, noS8R164_Law3640, noS8R164_Law3641, noS8R164_Law3642, noS8R164_Law3643, noS8R164_Law3644, noS8R164_Law3645, noS8R164_Law3646, noS8R164_Law3647, noS8R164_Law3648, noS8R164_Law3649, noS8R164_Law3650, noS8R164_Law3651, noS8R164_Law3652, noS8R164_Law3653, noS8R164_Law3654, noS8R164_Law3655, noS8R164_Law3656, noS8R164_Law3657, noS8R164_Law3658, noS8R164_Law3666, noS8R164_Law3669, noS8R164_Law3670, noS8R164_Law3671, noS8R164_Law3673, noS8R164_Law3676, noS8R164_Law3679, noS8R164_Law3680, noS8R164_Law3681, noS8R164_Law3683, noS8R164_Law3695, noS8R164_Law3696, noS8R164_Law3697, noS8R164_Law3698, noS8R164_Law3701, noS8R164_Law3702, noS8R164_Law3705, noS8R164_Law3706, noS8R164_Law3707, noS8R164_Law3708, noS8R164_Law3710, noS8R164_Law3711, noS8R164_Law3713, noS8R164_Law3716, noS8R164_Law3717, noS8R164_Law3718, noS8R164_Law3719, noS8R164_Law3720, noS8R164_Law3723, noS8R164_Law3726, noS8R164_Law3727, noS8R164_Law3728, noS8R164_Law3730, noS8R164_Law3731, noS8R164_Law3732, noS8R164_Law3733, noS8R164_Law3734, noS8R164_Law3735, noS8R164_Law3736, noS8R164_Law3738, noS8R164_Law3739, noS8R164_Law3741, noS8R164_Law3742, noS8R164_Law3743, noS8R164_Law3744, noS8R164_Law3745, noS8R164_Law3746, noS8R164_Law3747, noS8R164_Law3750, noS8R164_Law3753, noS8R164_Law3754, noS8R164_Law3755, noS8R164_Law3757, noS8R164_Law3760, noS8R164_Law3762, noS8R164_Law3763, noS8R164_Law3764⟩

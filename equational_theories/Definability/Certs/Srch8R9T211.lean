import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 212 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `44`
equations here, 2,215 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3625 takes them (73 nodes). -/
def ordS8R9_Law3625 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3625. -/
theorem noS8R9_Law3625 : ∀ v : Magma.tup8R9,
    ¬ @Equation3625 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3625) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3625) (by native_decide) v.1 v.2
    ((@Law3625.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3629 takes them (15 nodes). -/
def ordS8R9_Law3629 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3629. -/
theorem noS8R9_Law3629 : ∀ v : Magma.tup8R9,
    ¬ @Equation3629 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3629) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3629) (by native_decide) v.1 v.2
    ((@Law3629.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3634 takes them (372 nodes). -/
def ordS8R9_Law3634 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3634. -/
theorem noS8R9_Law3634 : ∀ v : Magma.tup8R9,
    ¬ @Equation3634 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3634) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3634) (by native_decide) v.1 v.2
    ((@Law3634.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3639 takes them (741 nodes). -/
def ordS8R9_Law3639 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3639. -/
theorem noS8R9_Law3639 : ∀ v : Magma.tup8R9,
    ¬ @Equation3639 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3639) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3639) (by native_decide) v.1 v.2
    ((@Law3639.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3644 takes them (13 nodes). -/
def ordS8R9_Law3644 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3644. -/
theorem noS8R9_Law3644 : ∀ v : Magma.tup8R9,
    ¬ @Equation3644 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3644) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3644) (by native_decide) v.1 v.2
    ((@Law3644.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3649 takes them (9 nodes). -/
def ordS8R9_Law3649 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3649. -/
theorem noS8R9_Law3649 : ∀ v : Magma.tup8R9,
    ¬ @Equation3649 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3649) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3649) (by native_decide) v.1 v.2
    ((@Law3649.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3654 takes them (13 nodes). -/
def ordS8R9_Law3654 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3654. -/
theorem noS8R9_Law3654 : ∀ v : Magma.tup8R9,
    ¬ @Equation3654 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3654) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3654) (by native_decide) v.1 v.2
    ((@Law3654.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3662 takes them (9 nodes). -/
def ordS8R9_Law3662 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3662. -/
theorem noS8R9_Law3662 : ∀ v : Magma.tup8R9,
    ¬ @Equation3662 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3662) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3662) (by native_decide) v.1 v.2
    ((@Law3662.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3663 takes them (9 nodes). -/
def ordS8R9_Law3663 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3663. -/
theorem noS8R9_Law3663 : ∀ v : Magma.tup8R9,
    ¬ @Equation3663 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3663) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3663) (by native_decide) v.1 v.2
    ((@Law3663.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3665 takes them (9 nodes). -/
def ordS8R9_Law3665 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3665. -/
theorem noS8R9_Law3665 : ∀ v : Magma.tup8R9,
    ¬ @Equation3665 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3665) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3665) (by native_decide) v.1 v.2
    ((@Law3665.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3666 takes them (9 nodes). -/
def ordS8R9_Law3666 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3666. -/
theorem noS8R9_Law3666 : ∀ v : Magma.tup8R9,
    ¬ @Equation3666 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3666) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3666) (by native_decide) v.1 v.2
    ((@Law3666.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3669 takes them (101 nodes). -/
def ordS8R9_Law3669 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3669. -/
theorem noS8R9_Law3669 : ∀ v : Magma.tup8R9,
    ¬ @Equation3669 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3669) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3669) (by native_decide) v.1 v.2
    ((@Law3669.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3670 takes them (192 nodes). -/
def ordS8R9_Law3670 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3670. -/
theorem noS8R9_Law3670 : ∀ v : Magma.tup8R9,
    ¬ @Equation3670 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3670) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3670) (by native_decide) v.1 v.2
    ((@Law3670.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3671 takes them (9 nodes). -/
def ordS8R9_Law3671 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3671. -/
theorem noS8R9_Law3671 : ∀ v : Magma.tup8R9,
    ¬ @Equation3671 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3671) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3671) (by native_decide) v.1 v.2
    ((@Law3671.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3672 takes them (9 nodes). -/
def ordS8R9_Law3672 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3672. -/
theorem noS8R9_Law3672 : ∀ v : Magma.tup8R9,
    ¬ @Equation3672 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3672) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3672) (by native_decide) v.1 v.2
    ((@Law3672.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3673 takes them (9 nodes). -/
def ordS8R9_Law3673 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3673. -/
theorem noS8R9_Law3673 : ∀ v : Magma.tup8R9,
    ¬ @Equation3673 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3673) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3673) (by native_decide) v.1 v.2
    ((@Law3673.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3677 takes them (9 nodes). -/
def ordS8R9_Law3677 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3677. -/
theorem noS8R9_Law3677 : ∀ v : Magma.tup8R9,
    ¬ @Equation3677 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3677) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3677) (by native_decide) v.1 v.2
    ((@Law3677.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3680 takes them (9 nodes). -/
def ordS8R9_Law3680 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3680. -/
theorem noS8R9_Law3680 : ∀ v : Magma.tup8R9,
    ¬ @Equation3680 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3680) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3680) (by native_decide) v.1 v.2
    ((@Law3680.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3684 takes them (9 nodes). -/
def ordS8R9_Law3684 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3684. -/
theorem noS8R9_Law3684 : ∀ v : Magma.tup8R9,
    ¬ @Equation3684 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3684) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3684) (by native_decide) v.1 v.2
    ((@Law3684.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3690 takes them (9 nodes). -/
def ordS8R9_Law3690 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3690. -/
theorem noS8R9_Law3690 : ∀ v : Magma.tup8R9,
    ¬ @Equation3690 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3690) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3690) (by native_decide) v.1 v.2
    ((@Law3690.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3694 takes them (9 nodes). -/
def ordS8R9_Law3694 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3694. -/
theorem noS8R9_Law3694 : ∀ v : Magma.tup8R9,
    ¬ @Equation3694 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3694) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3694) (by native_decide) v.1 v.2
    ((@Law3694.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3698 takes them (9 nodes). -/
def ordS8R9_Law3698 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3698. -/
theorem noS8R9_Law3698 : ∀ v : Magma.tup8R9,
    ¬ @Equation3698 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3698) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3698) (by native_decide) v.1 v.2
    ((@Law3698.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3702 takes them (101 nodes). -/
def ordS8R9_Law3702 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3702. -/
theorem noS8R9_Law3702 : ∀ v : Magma.tup8R9,
    ¬ @Equation3702 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3702) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3702) (by native_decide) v.1 v.2
    ((@Law3702.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3706 takes them (9 nodes). -/
def ordS8R9_Law3706 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3706. -/
theorem noS8R9_Law3706 : ∀ v : Magma.tup8R9,
    ¬ @Equation3706 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3706) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3706) (by native_decide) v.1 v.2
    ((@Law3706.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3711 takes them (9 nodes). -/
def ordS8R9_Law3711 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3711. -/
theorem noS8R9_Law3711 : ∀ v : Magma.tup8R9,
    ¬ @Equation3711 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3711) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3711) (by native_decide) v.1 v.2
    ((@Law3711.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3713 takes them (9 nodes). -/
def ordS8R9_Law3713 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3713. -/
theorem noS8R9_Law3713 : ∀ v : Magma.tup8R9,
    ¬ @Equation3713 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3713) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3713) (by native_decide) v.1 v.2
    ((@Law3713.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3717 takes them (9 nodes). -/
def ordS8R9_Law3717 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3717. -/
theorem noS8R9_Law3717 : ∀ v : Magma.tup8R9,
    ¬ @Equation3717 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3717) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3717) (by native_decide) v.1 v.2
    ((@Law3717.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3719 takes them (9 nodes). -/
def ordS8R9_Law3719 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3719. -/
theorem noS8R9_Law3719 : ∀ v : Magma.tup8R9,
    ¬ @Equation3719 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3719) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3719) (by native_decide) v.1 v.2
    ((@Law3719.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3720 takes them (9 nodes). -/
def ordS8R9_Law3720 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3720. -/
theorem noS8R9_Law3720 : ∀ v : Magma.tup8R9,
    ¬ @Equation3720 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3720) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3720) (by native_decide) v.1 v.2
    ((@Law3720.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3727 takes them (44 nodes). -/
def ordS8R9_Law3727 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3727. -/
theorem noS8R9_Law3727 : ∀ v : Magma.tup8R9,
    ¬ @Equation3727 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3727) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3727) (by native_decide) v.1 v.2
    ((@Law3727.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3729 takes them (9 nodes). -/
def ordS8R9_Law3729 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3729. -/
theorem noS8R9_Law3729 : ∀ v : Magma.tup8R9,
    ¬ @Equation3729 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3729) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3729) (by native_decide) v.1 v.2
    ((@Law3729.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3730 takes them (9 nodes). -/
def ordS8R9_Law3730 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3730. -/
theorem noS8R9_Law3730 : ∀ v : Magma.tup8R9,
    ¬ @Equation3730 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3730) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3730) (by native_decide) v.1 v.2
    ((@Law3730.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3731 takes them (9 nodes). -/
def ordS8R9_Law3731 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3731. -/
theorem noS8R9_Law3731 : ∀ v : Magma.tup8R9,
    ¬ @Equation3731 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3731) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3731) (by native_decide) v.1 v.2
    ((@Law3731.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3733 takes them (9 nodes). -/
def ordS8R9_Law3733 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3733. -/
theorem noS8R9_Law3733 : ∀ v : Magma.tup8R9,
    ¬ @Equation3733 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3733) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3733) (by native_decide) v.1 v.2
    ((@Law3733.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3734 takes them (9 nodes). -/
def ordS8R9_Law3734 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3734. -/
theorem noS8R9_Law3734 : ∀ v : Magma.tup8R9,
    ¬ @Equation3734 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3734) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3734) (by native_decide) v.1 v.2
    ((@Law3734.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3735 takes them (29 nodes). -/
def ordS8R9_Law3735 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3735. -/
theorem noS8R9_Law3735 : ∀ v : Magma.tup8R9,
    ¬ @Equation3735 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3735) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3735) (by native_decide) v.1 v.2
    ((@Law3735.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3737 takes them (9 nodes). -/
def ordS8R9_Law3737 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3737. -/
theorem noS8R9_Law3737 : ∀ v : Magma.tup8R9,
    ¬ @Equation3737 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3737) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3737) (by native_decide) v.1 v.2
    ((@Law3737.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3738 takes them (9 nodes). -/
def ordS8R9_Law3738 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3738. -/
theorem noS8R9_Law3738 : ∀ v : Magma.tup8R9,
    ¬ @Equation3738 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3738) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3738) (by native_decide) v.1 v.2
    ((@Law3738.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3739 takes them (9 nodes). -/
def ordS8R9_Law3739 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3739. -/
theorem noS8R9_Law3739 : ∀ v : Magma.tup8R9,
    ¬ @Equation3739 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3739) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3739) (by native_decide) v.1 v.2
    ((@Law3739.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3740 takes them (128 nodes). -/
def ordS8R9_Law3740 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3740. -/
theorem noS8R9_Law3740 : ∀ v : Magma.tup8R9,
    ¬ @Equation3740 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3740) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3740) (by native_decide) v.1 v.2
    ((@Law3740.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3741 takes them (9 nodes). -/
def ordS8R9_Law3741 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3741. -/
theorem noS8R9_Law3741 : ∀ v : Magma.tup8R9,
    ¬ @Equation3741 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3741) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3741) (by native_decide) v.1 v.2
    ((@Law3741.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3742 takes them (9 nodes). -/
def ordS8R9_Law3742 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3742. -/
theorem noS8R9_Law3742 : ∀ v : Magma.tup8R9,
    ¬ @Equation3742 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3742) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3742) (by native_decide) v.1 v.2
    ((@Law3742.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3743 takes them (9 nodes). -/
def ordS8R9_Law3743 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3743. -/
theorem noS8R9_Law3743 : ∀ v : Magma.tup8R9,
    ¬ @Equation3743 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3743) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3743) (by native_decide) v.1 v.2
    ((@Law3743.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3744 takes them (114 nodes). -/
def ordS8R9_Law3744 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3744. -/
theorem noS8R9_Law3744 : ∀ v : Magma.tup8R9,
    ¬ @Equation3744 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3744) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3744) (by native_decide) v.1 v.2
    ((@Law3744.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `44` equations. -/
theorem srch8R9_refutes_211 :
    FamilyRefutes Magma.srch8R9 [
      3625, 3629, 3634, 3639, 3644, 3649, 3654, 3662, 3663, 3665, 3666, 3669, 3670, 3671, 3672,
      3673, 3677, 3680, 3684, 3690, 3694, 3698, 3702, 3706, 3711, 3713, 3717, 3719, 3720, 3727,
      3729, 3730, 3731, 3733, 3734, 3735, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744
    ] :=
  ⟨noS8R9_Law3625, noS8R9_Law3629, noS8R9_Law3634, noS8R9_Law3639, noS8R9_Law3644, noS8R9_Law3649, noS8R9_Law3654, noS8R9_Law3662, noS8R9_Law3663, noS8R9_Law3665, noS8R9_Law3666, noS8R9_Law3669, noS8R9_Law3670, noS8R9_Law3671, noS8R9_Law3672, noS8R9_Law3673, noS8R9_Law3677, noS8R9_Law3680, noS8R9_Law3684, noS8R9_Law3690, noS8R9_Law3694, noS8R9_Law3698, noS8R9_Law3702, noS8R9_Law3706, noS8R9_Law3711, noS8R9_Law3713, noS8R9_Law3717, noS8R9_Law3719, noS8R9_Law3720, noS8R9_Law3727, noS8R9_Law3729, noS8R9_Law3730, noS8R9_Law3731, noS8R9_Law3733, noS8R9_Law3734, noS8R9_Law3735, noS8R9_Law3737, noS8R9_Law3738, noS8R9_Law3739, noS8R9_Law3740, noS8R9_Law3741, noS8R9_Law3742, noS8R9_Law3743, noS8R9_Law3744⟩

import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 7 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 306 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3541 takes them (4 nodes). -/
def ordS11R173_Law3541 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3541. -/
theorem noS11R173_Law3541 : ∀ v : Magma.tup11R173,
    ¬ @Equation3541 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3541) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3541) (by native_decide) v.1 v.2
    ((@Law3541.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3542 takes them (3 nodes). -/
def ordS11R173_Law3542 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3542. -/
theorem noS11R173_Law3542 : ∀ v : Magma.tup11R173,
    ¬ @Equation3542 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3542) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3542) (by native_decide) v.1 v.2
    ((@Law3542.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3543 takes them (3 nodes). -/
def ordS11R173_Law3543 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3543. -/
theorem noS11R173_Law3543 : ∀ v : Magma.tup11R173,
    ¬ @Equation3543 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3543) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3543) (by native_decide) v.1 v.2
    ((@Law3543.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3546 takes them (3 nodes). -/
def ordS11R173_Law3546 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3546. -/
theorem noS11R173_Law3546 : ∀ v : Magma.tup11R173,
    ¬ @Equation3546 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3546) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3546) (by native_decide) v.1 v.2
    ((@Law3546.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (3 nodes). -/
def ordS11R173_Law3549 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3549. -/
theorem noS11R173_Law3549 : ∀ v : Magma.tup11R173,
    ¬ @Equation3549 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3660 takes them (3 nodes). -/
def ordS11R173_Law3660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3660. -/
theorem noS11R173_Law3660 : ∀ v : Magma.tup11R173,
    ¬ @Equation3660 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3660) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3660) (by native_decide) v.1 v.2
    ((@Law3660.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3661 takes them (4 nodes). -/
def ordS11R173_Law3661 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3661. -/
theorem noS11R173_Law3661 : ∀ v : Magma.tup11R173,
    ¬ @Equation3661 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3661) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3661) (by native_decide) v.1 v.2
    ((@Law3661.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3664 takes them (4 nodes). -/
def ordS11R173_Law3664 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3664. -/
theorem noS11R173_Law3664 : ∀ v : Magma.tup11R173,
    ¬ @Equation3664 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3664) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3664) (by native_decide) v.1 v.2
    ((@Law3664.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3674 takes them (3 nodes). -/
def ordS11R173_Law3674 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3674. -/
theorem noS11R173_Law3674 : ∀ v : Magma.tup11R173,
    ¬ @Equation3674 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3674) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3674) (by native_decide) v.1 v.2
    ((@Law3674.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3712 takes them (4 nodes). -/
def ordS11R173_Law3712 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3712. -/
theorem noS11R173_Law3712 : ∀ v : Magma.tup11R173,
    ¬ @Equation3712 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3712) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3712) (by native_decide) v.1 v.2
    ((@Law3712.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (3 nodes). -/
def ordS11R173_Law3714 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3714. -/
theorem noS11R173_Law3714 : ∀ v : Magma.tup11R173,
    ¬ @Equation3714 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3721 takes them (3 nodes). -/
def ordS11R173_Law3721 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3721. -/
theorem noS11R173_Law3721 : ∀ v : Magma.tup11R173,
    ¬ @Equation3721 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3721) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3721) (by native_decide) v.1 v.2
    ((@Law3721.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3723 takes them (3 nodes). -/
def ordS11R173_Law3723 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3723. -/
theorem noS11R173_Law3723 : ∀ v : Magma.tup11R173,
    ¬ @Equation3723 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3723) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3723) (by native_decide) v.1 v.2
    ((@Law3723.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3725 takes them (4 nodes). -/
def ordS11R173_Law3725 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3725. -/
theorem noS11R173_Law3725 : ∀ v : Magma.tup11R173,
    ¬ @Equation3725 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3725) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3725) (by native_decide) v.1 v.2
    ((@Law3725.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3728 takes them (4 nodes). -/
def ordS11R173_Law3728 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3728. -/
theorem noS11R173_Law3728 : ∀ v : Magma.tup11R173,
    ¬ @Equation3728 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3728) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3728) (by native_decide) v.1 v.2
    ((@Law3728.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3732 takes them (4 nodes). -/
def ordS11R173_Law3732 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3732. -/
theorem noS11R173_Law3732 : ∀ v : Magma.tup11R173,
    ¬ @Equation3732 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3732) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3732) (by native_decide) v.1 v.2
    ((@Law3732.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (3 nodes). -/
def ordS11R173_Law3752 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3752. -/
theorem noS11R173_Law3752 : ∀ v : Magma.tup11R173,
    ¬ @Equation3752 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3759 takes them (3 nodes). -/
def ordS11R173_Law3759 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3759. -/
theorem noS11R173_Law3759 : ∀ v : Magma.tup11R173,
    ¬ @Equation3759 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3759) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3759) (by native_decide) v.1 v.2
    ((@Law3759.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3803 takes them (3 nodes). -/
def ordS11R173_Law3803 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3803. -/
theorem noS11R173_Law3803 : ∀ v : Magma.tup11R173,
    ¬ @Equation3803 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3803) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3803) (by native_decide) v.1 v.2
    ((@Law3803.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3864 takes them (4 nodes). -/
def ordS11R173_Law3864 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3864. -/
theorem noS11R173_Law3864 : ∀ v : Magma.tup11R173,
    ¬ @Equation3864 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3864) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3864) (by native_decide) v.1 v.2
    ((@Law3864.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3867 takes them (4 nodes). -/
def ordS11R173_Law3867 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3867. -/
theorem noS11R173_Law3867 : ∀ v : Magma.tup11R173,
    ¬ @Equation3867 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3867) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3867) (by native_decide) v.1 v.2
    ((@Law3867.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3868 takes them (3 nodes). -/
def ordS11R173_Law3868 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3868. -/
theorem noS11R173_Law3868 : ∀ v : Magma.tup11R173,
    ¬ @Equation3868 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3870 takes them (4 nodes). -/
def ordS11R173_Law3870 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3870. -/
theorem noS11R173_Law3870 : ∀ v : Magma.tup11R173,
    ¬ @Equation3870 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3870) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3870) (by native_decide) v.1 v.2
    ((@Law3870.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3873 takes them (4 nodes). -/
def ordS11R173_Law3873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3873. -/
theorem noS11R173_Law3873 : ∀ v : Magma.tup11R173,
    ¬ @Equation3873 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3873) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3873) (by native_decide) v.1 v.2
    ((@Law3873.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3877 takes them (3 nodes). -/
def ordS11R173_Law3877 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3877. -/
theorem noS11R173_Law3877 : ∀ v : Magma.tup11R173,
    ¬ @Equation3877 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3877) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3877) (by native_decide) v.1 v.2
    ((@Law3877.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (3 nodes). -/
def ordS11R173_Law3880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3880. -/
theorem noS11R173_Law3880 : ∀ v : Magma.tup11R173,
    ¬ @Equation3880 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3883 takes them (3 nodes). -/
def ordS11R173_Law3883 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3883. -/
theorem noS11R173_Law3883 : ∀ v : Magma.tup11R173,
    ¬ @Equation3883 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3883) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3883) (by native_decide) v.1 v.2
    ((@Law3883.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3890 takes them (3 nodes). -/
def ordS11R173_Law3890 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3890. -/
theorem noS11R173_Law3890 : ∀ v : Magma.tup11R173,
    ¬ @Equation3890 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3890) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3890) (by native_decide) v.1 v.2
    ((@Law3890.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3893 takes them (3 nodes). -/
def ordS11R173_Law3893 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3893. -/
theorem noS11R173_Law3893 : ∀ v : Magma.tup11R173,
    ¬ @Equation3893 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3893) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3893) (by native_decide) v.1 v.2
    ((@Law3893.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3897 takes them (3 nodes). -/
def ordS11R173_Law3897 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3897. -/
theorem noS11R173_Law3897 : ∀ v : Magma.tup11R173,
    ¬ @Equation3897 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3897) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3897) (by native_decide) v.1 v.2
    ((@Law3897.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3901 takes them (3 nodes). -/
def ordS11R173_Law3901 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3901. -/
theorem noS11R173_Law3901 : ∀ v : Magma.tup11R173,
    ¬ @Equation3901 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3901) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3901) (by native_decide) v.1 v.2
    ((@Law3901.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3905 takes them (3 nodes). -/
def ordS11R173_Law3905 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3905. -/
theorem noS11R173_Law3905 : ∀ v : Magma.tup11R173,
    ¬ @Equation3905 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3905) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3905) (by native_decide) v.1 v.2
    ((@Law3905.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3909 takes them (3 nodes). -/
def ordS11R173_Law3909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3909. -/
theorem noS11R173_Law3909 : ∀ v : Magma.tup11R173,
    ¬ @Equation3909 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3909) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3909) (by native_decide) v.1 v.2
    ((@Law3909.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (3 nodes). -/
def ordS11R173_Law3917 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3917. -/
theorem noS11R173_Law3917 : ∀ v : Magma.tup11R173,
    ¬ @Equation3917 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3918 takes them (4 nodes). -/
def ordS11R173_Law3918 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3918. -/
theorem noS11R173_Law3918 : ∀ v : Magma.tup11R173,
    ¬ @Equation3918 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3918) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3918) (by native_decide) v.1 v.2
    ((@Law3918.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3921 takes them (4 nodes). -/
def ordS11R173_Law3921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3921. -/
theorem noS11R173_Law3921 : ∀ v : Magma.tup11R173,
    ¬ @Equation3921 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3921) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3921) (by native_decide) v.1 v.2
    ((@Law3921.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3925 takes them (4 nodes). -/
def ordS11R173_Law3925 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3925. -/
theorem noS11R173_Law3925 : ∀ v : Magma.tup11R173,
    ¬ @Equation3925 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3925) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3925) (by native_decide) v.1 v.2
    ((@Law3925.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (3 nodes). -/
def ordS11R173_Law3927 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3927. -/
theorem noS11R173_Law3927 : ∀ v : Magma.tup11R173,
    ¬ @Equation3927 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3928 takes them (4 nodes). -/
def ordS11R173_Law3928 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3928. -/
theorem noS11R173_Law3928 : ∀ v : Magma.tup11R173,
    ¬ @Equation3928 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3928) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3928) (by native_decide) v.1 v.2
    ((@Law3928.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (4 nodes). -/
def ordS11R173_Law3931 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3931. -/
theorem noS11R173_Law3931 : ∀ v : Magma.tup11R173,
    ¬ @Equation3931 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3935 takes them (4 nodes). -/
def ordS11R173_Law3935 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3935. -/
theorem noS11R173_Law3935 : ∀ v : Magma.tup11R173,
    ¬ @Equation3935 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3935) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3935) (by native_decide) v.1 v.2
    ((@Law3935.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3939 takes them (4 nodes). -/
def ordS11R173_Law3939 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3939. -/
theorem noS11R173_Law3939 : ∀ v : Magma.tup11R173,
    ¬ @Equation3939 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3939) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3939) (by native_decide) v.1 v.2
    ((@Law3939.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3943 takes them (4 nodes). -/
def ordS11R173_Law3943 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3943. -/
theorem noS11R173_Law3943 : ∀ v : Magma.tup11R173,
    ¬ @Equation3943 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3943) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3943) (by native_decide) v.1 v.2
    ((@Law3943.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (4 nodes). -/
def ordS11R173_Law3947 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3947. -/
theorem noS11R173_Law3947 : ∀ v : Magma.tup11R173,
    ¬ @Equation3947 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (3 nodes). -/
def ordS11R173_Law3952 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3952. -/
theorem noS11R173_Law3952 : ∀ v : Magma.tup11R173,
    ¬ @Equation3952 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (3 nodes). -/
def ordS11R173_Law3955 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3955. -/
theorem noS11R173_Law3955 : ∀ v : Magma.tup11R173,
    ¬ @Equation3955 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3958 takes them (3 nodes). -/
def ordS11R173_Law3958 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3958. -/
theorem noS11R173_Law3958 : ∀ v : Magma.tup11R173,
    ¬ @Equation3958 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3958) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3958) (by native_decide) v.1 v.2
    ((@Law3958.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3965 takes them (3 nodes). -/
def ordS11R173_Law3965 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3965. -/
theorem noS11R173_Law3965 : ∀ v : Magma.tup11R173,
    ¬ @Equation3965 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3965) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3965) (by native_decide) v.1 v.2
    ((@Law3965.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3968 takes them (3 nodes). -/
def ordS11R173_Law3968 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3968. -/
theorem noS11R173_Law3968 : ∀ v : Magma.tup11R173,
    ¬ @Equation3968 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3968) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3968) (by native_decide) v.1 v.2
    ((@Law3968.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (3 nodes). -/
def ordS11R173_Law3972 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3972. -/
theorem noS11R173_Law3972 : ∀ v : Magma.tup11R173,
    ¬ @Equation3972 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3976 takes them (3 nodes). -/
def ordS11R173_Law3976 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3976. -/
theorem noS11R173_Law3976 : ∀ v : Magma.tup11R173,
    ¬ @Equation3976 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3976) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3976) (by native_decide) v.1 v.2
    ((@Law3976.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3980 takes them (3 nodes). -/
def ordS11R173_Law3980 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3980. -/
theorem noS11R173_Law3980 : ∀ v : Magma.tup11R173,
    ¬ @Equation3980 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3980) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3980) (by native_decide) v.1 v.2
    ((@Law3980.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3984 takes them (3 nodes). -/
def ordS11R173_Law3984 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3984. -/
theorem noS11R173_Law3984 : ∀ v : Magma.tup11R173,
    ¬ @Equation3984 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3984) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3984) (by native_decide) v.1 v.2
    ((@Law3984.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (3 nodes). -/
def ordS11R173_Law3989 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3989. -/
theorem noS11R173_Law3989 : ∀ v : Magma.tup11R173,
    ¬ @Equation3989 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3993 takes them (3 nodes). -/
def ordS11R173_Law3993 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3993. -/
theorem noS11R173_Law3993 : ∀ v : Magma.tup11R173,
    ¬ @Equation3993 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3993) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3993) (by native_decide) v.1 v.2
    ((@Law3993.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (3 nodes). -/
def ordS11R173_Law3997 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3997. -/
theorem noS11R173_Law3997 : ∀ v : Magma.tup11R173,
    ¬ @Equation3997 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4001 takes them (3 nodes). -/
def ordS11R173_Law4001 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4001. -/
theorem noS11R173_Law4001 : ∀ v : Magma.tup11R173,
    ¬ @Equation4001 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4001) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4001) (by native_decide) v.1 v.2
    ((@Law4001.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4006 takes them (3 nodes). -/
def ordS11R173_Law4006 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4006. -/
theorem noS11R173_Law4006 : ∀ v : Magma.tup11R173,
    ¬ @Equation4006 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4010 takes them (3 nodes). -/
def ordS11R173_Law4010 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4010. -/
theorem noS11R173_Law4010 : ∀ v : Magma.tup11R173,
    ¬ @Equation4010 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4010) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4010) (by native_decide) v.1 v.2
    ((@Law4010.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4014 takes them (3 nodes). -/
def ordS11R173_Law4014 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4014. -/
theorem noS11R173_Law4014 : ∀ v : Magma.tup11R173,
    ¬ @Equation4014 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4014) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4014) (by native_decide) v.1 v.2
    ((@Law4014.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4018 takes them (3 nodes). -/
def ordS11R173_Law4018 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4018. -/
theorem noS11R173_Law4018 : ∀ v : Magma.tup11R173,
    ¬ @Equation4018 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4018) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4018) (by native_decide) v.1 v.2
    ((@Law4018.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4027 takes them (3 nodes). -/
def ordS11R173_Law4027 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4027. -/
theorem noS11R173_Law4027 : ∀ v : Magma.tup11R173,
    ¬ @Equation4027 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4027) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4027) (by native_decide) v.1 v.2
    ((@Law4027.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4031 takes them (3 nodes). -/
def ordS11R173_Law4031 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4031. -/
theorem noS11R173_Law4031 : ∀ v : Magma.tup11R173,
    ¬ @Equation4031 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4031) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4031) (by native_decide) v.1 v.2
    ((@Law4031.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4035 takes them (3 nodes). -/
def ordS11R173_Law4035 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4035. -/
theorem noS11R173_Law4035 : ∀ v : Magma.tup11R173,
    ¬ @Equation4035 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4035) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4035) (by native_decide) v.1 v.2
    ((@Law4035.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (3 nodes). -/
def ordS11R173_Law4040 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4040. -/
theorem noS11R173_Law4040 : ∀ v : Magma.tup11R173,
    ¬ @Equation4040 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4045 takes them (3 nodes). -/
def ordS11R173_Law4045 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4045. -/
theorem noS11R173_Law4045 : ∀ v : Magma.tup11R173,
    ¬ @Equation4045 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4045) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4045) (by native_decide) v.1 v.2
    ((@Law4045.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4050 takes them (3 nodes). -/
def ordS11R173_Law4050 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4050. -/
theorem noS11R173_Law4050 : ∀ v : Magma.tup11R173,
    ¬ @Equation4050 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4050) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4050) (by native_decide) v.1 v.2
    ((@Law4050.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4055 takes them (3 nodes). -/
def ordS11R173_Law4055 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4055. -/
theorem noS11R173_Law4055 : ∀ v : Magma.tup11R173,
    ¬ @Equation4055 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4055) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4055) (by native_decide) v.1 v.2
    ((@Law4055.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4067 takes them (4 nodes). -/
def ordS11R173_Law4067 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4067. -/
theorem noS11R173_Law4067 : ∀ v : Magma.tup11R173,
    ¬ @Equation4067 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4067) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4067) (by native_decide) v.1 v.2
    ((@Law4067.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4070 takes them (4 nodes). -/
def ordS11R173_Law4070 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4070. -/
theorem noS11R173_Law4070 : ∀ v : Magma.tup11R173,
    ¬ @Equation4070 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4070) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4070) (by native_decide) v.1 v.2
    ((@Law4070.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4071 takes them (3 nodes). -/
def ordS11R173_Law4071 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4071. -/
theorem noS11R173_Law4071 : ∀ v : Magma.tup11R173,
    ¬ @Equation4071 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (3 nodes). -/
def ordS11R173_Law4074 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4074. -/
theorem noS11R173_Law4074 : ∀ v : Magma.tup11R173,
    ¬ @Equation4074 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4076 takes them (4 nodes). -/
def ordS11R173_Law4076 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4076. -/
theorem noS11R173_Law4076 : ∀ v : Magma.tup11R173,
    ¬ @Equation4076 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4076) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4076) (by native_decide) v.1 v.2
    ((@Law4076.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4080 takes them (3 nodes). -/
def ordS11R173_Law4080 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4080. -/
theorem noS11R173_Law4080 : ∀ v : Magma.tup11R173,
    ¬ @Equation4080 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4080) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4080) (by native_decide) v.1 v.2
    ((@Law4080.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (3 nodes). -/
def ordS11R173_Law4083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4083. -/
theorem noS11R173_Law4083 : ∀ v : Magma.tup11R173,
    ¬ @Equation4083 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4086 takes them (3 nodes). -/
def ordS11R173_Law4086 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4086. -/
theorem noS11R173_Law4086 : ∀ v : Magma.tup11R173,
    ¬ @Equation4086 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4086) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4086) (by native_decide) v.1 v.2
    ((@Law4086.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4090 takes them (3 nodes). -/
def ordS11R173_Law4090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4090. -/
theorem noS11R173_Law4090 : ∀ v : Magma.tup11R173,
    ¬ @Equation4090 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4090) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4090) (by native_decide) v.1 v.2
    ((@Law4090.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4093 takes them (3 nodes). -/
def ordS11R173_Law4093 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4093. -/
theorem noS11R173_Law4093 : ∀ v : Magma.tup11R173,
    ¬ @Equation4093 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4093) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4093) (by native_decide) v.1 v.2
    ((@Law4093.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4096 takes them (3 nodes). -/
def ordS11R173_Law4096 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4096. -/
theorem noS11R173_Law4096 : ∀ v : Magma.tup11R173,
    ¬ @Equation4096 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4096) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4096) (by native_decide) v.1 v.2
    ((@Law4096.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4100 takes them (3 nodes). -/
def ordS11R173_Law4100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4100. -/
theorem noS11R173_Law4100 : ∀ v : Magma.tup11R173,
    ¬ @Equation4100 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4100) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4100) (by native_decide) v.1 v.2
    ((@Law4100.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (3 nodes). -/
def ordS11R173_Law4104 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4104. -/
theorem noS11R173_Law4104 : ∀ v : Magma.tup11R173,
    ¬ @Equation4104 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4108 takes them (3 nodes). -/
def ordS11R173_Law4108 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4108. -/
theorem noS11R173_Law4108 : ∀ v : Magma.tup11R173,
    ¬ @Equation4108 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4108) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4108) (by native_decide) v.1 v.2
    ((@Law4108.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4112 takes them (3 nodes). -/
def ordS11R173_Law4112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4112. -/
theorem noS11R173_Law4112 : ∀ v : Magma.tup11R173,
    ¬ @Equation4112 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4112) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4112) (by native_decide) v.1 v.2
    ((@Law4112.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4120 takes them (3 nodes). -/
def ordS11R173_Law4120 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4120. -/
theorem noS11R173_Law4120 : ∀ v : Magma.tup11R173,
    ¬ @Equation4120 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4120) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4120) (by native_decide) v.1 v.2
    ((@Law4120.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4121 takes them (4 nodes). -/
def ordS11R173_Law4121 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4121. -/
theorem noS11R173_Law4121 : ∀ v : Magma.tup11R173,
    ¬ @Equation4121 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4121) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4121) (by native_decide) v.1 v.2
    ((@Law4121.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4124 takes them (4 nodes). -/
def ordS11R173_Law4124 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4124. -/
theorem noS11R173_Law4124 : ∀ v : Magma.tup11R173,
    ¬ @Equation4124 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4124) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4124) (by native_decide) v.1 v.2
    ((@Law4124.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4128 takes them (4 nodes). -/
def ordS11R173_Law4128 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4128. -/
theorem noS11R173_Law4128 : ∀ v : Magma.tup11R173,
    ¬ @Equation4128 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4128) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4128) (by native_decide) v.1 v.2
    ((@Law4128.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4134 takes them (4 nodes). -/
def ordS11R173_Law4134 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4134. -/
theorem noS11R173_Law4134 : ∀ v : Magma.tup11R173,
    ¬ @Equation4134 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4134) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4134) (by native_decide) v.1 v.2
    ((@Law4134.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4138 takes them (4 nodes). -/
def ordS11R173_Law4138 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4138. -/
theorem noS11R173_Law4138 : ∀ v : Magma.tup11R173,
    ¬ @Equation4138 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4138) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4138) (by native_decide) v.1 v.2
    ((@Law4138.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4142 takes them (4 nodes). -/
def ordS11R173_Law4142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4142. -/
theorem noS11R173_Law4142 : ∀ v : Magma.tup11R173,
    ¬ @Equation4142 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4142) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4142) (by native_decide) v.1 v.2
    ((@Law4142.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4143 takes them (3 nodes). -/
def ordS11R173_Law4143 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4143. -/
theorem noS11R173_Law4143 : ∀ v : Magma.tup11R173,
    ¬ @Equation4143 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4150 takes them (4 nodes). -/
def ordS11R173_Law4150 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4150. -/
theorem noS11R173_Law4150 : ∀ v : Magma.tup11R173,
    ¬ @Equation4150 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4150) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4150) (by native_decide) v.1 v.2
    ((@Law4150.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_6 :
    FamilyRefutes Magma.srch11R173 [
      3541, 3542, 3543, 3546, 3549, 3660, 3661, 3664, 3674, 3712, 3714, 3721, 3723, 3725, 3728,
      3732, 3752, 3759, 3803, 3864, 3867, 3868, 3870, 3873, 3877, 3880, 3883, 3890, 3893, 3897,
      3901, 3905, 3909, 3917, 3918, 3921, 3925, 3927, 3928, 3931, 3935, 3939, 3943, 3947, 3952,
      3955, 3958, 3965, 3968, 3972, 3976, 3980, 3984, 3989, 3993, 3997, 4001, 4006, 4010, 4014,
      4018, 4027, 4031, 4035, 4040, 4045, 4050, 4055, 4067, 4070, 4071, 4074, 4076, 4080, 4083,
      4086, 4090, 4093, 4096, 4100, 4104, 4108, 4112, 4120, 4121, 4124, 4128, 4134, 4138, 4142,
      4143, 4150
    ] :=
  ⟨noS11R173_Law3541, noS11R173_Law3542, noS11R173_Law3543, noS11R173_Law3546, noS11R173_Law3549, noS11R173_Law3660, noS11R173_Law3661, noS11R173_Law3664, noS11R173_Law3674, noS11R173_Law3712, noS11R173_Law3714, noS11R173_Law3721, noS11R173_Law3723, noS11R173_Law3725, noS11R173_Law3728, noS11R173_Law3732, noS11R173_Law3752, noS11R173_Law3759, noS11R173_Law3803, noS11R173_Law3864, noS11R173_Law3867, noS11R173_Law3868, noS11R173_Law3870, noS11R173_Law3873, noS11R173_Law3877, noS11R173_Law3880, noS11R173_Law3883, noS11R173_Law3890, noS11R173_Law3893, noS11R173_Law3897, noS11R173_Law3901, noS11R173_Law3905, noS11R173_Law3909, noS11R173_Law3917, noS11R173_Law3918, noS11R173_Law3921, noS11R173_Law3925, noS11R173_Law3927, noS11R173_Law3928, noS11R173_Law3931, noS11R173_Law3935, noS11R173_Law3939, noS11R173_Law3943, noS11R173_Law3947, noS11R173_Law3952, noS11R173_Law3955, noS11R173_Law3958, noS11R173_Law3965, noS11R173_Law3968, noS11R173_Law3972, noS11R173_Law3976, noS11R173_Law3980, noS11R173_Law3984, noS11R173_Law3989, noS11R173_Law3993, noS11R173_Law3997, noS11R173_Law4001, noS11R173_Law4006, noS11R173_Law4010, noS11R173_Law4014, noS11R173_Law4018, noS11R173_Law4027, noS11R173_Law4031, noS11R173_Law4035, noS11R173_Law4040, noS11R173_Law4045, noS11R173_Law4050, noS11R173_Law4055, noS11R173_Law4067, noS11R173_Law4070, noS11R173_Law4071, noS11R173_Law4074, noS11R173_Law4076, noS11R173_Law4080, noS11R173_Law4083, noS11R173_Law4086, noS11R173_Law4090, noS11R173_Law4093, noS11R173_Law4096, noS11R173_Law4100, noS11R173_Law4104, noS11R173_Law4108, noS11R173_Law4112, noS11R173_Law4120, noS11R173_Law4121, noS11R173_Law4124, noS11R173_Law4128, noS11R173_Law4134, noS11R173_Law4138, noS11R173_Law4142, noS11R173_Law4143, noS11R173_Law4150⟩

import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 213 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `31`
equations here, 2,681 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3745 takes them (9 nodes). -/
def ordS8R9_Law3745 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3745. -/
theorem noS8R9_Law3745 : ∀ v : Magma.tup8R9,
    ¬ @Equation3745 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3745) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3745) (by native_decide) v.1 v.2
    ((@Law3745.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3746 takes them (9 nodes). -/
def ordS8R9_Law3746 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3746. -/
theorem noS8R9_Law3746 : ∀ v : Magma.tup8R9,
    ¬ @Equation3746 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3746) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3746) (by native_decide) v.1 v.2
    ((@Law3746.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3747 takes them (9 nodes). -/
def ordS8R9_Law3747 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3747. -/
theorem noS8R9_Law3747 : ∀ v : Magma.tup8R9,
    ¬ @Equation3747 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3747) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3747) (by native_decide) v.1 v.2
    ((@Law3747.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3755 takes them (29 nodes). -/
def ordS8R9_Law3755 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3755. -/
theorem noS8R9_Law3755 : ∀ v : Magma.tup8R9,
    ¬ @Equation3755 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3755) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3755) (by native_decide) v.1 v.2
    ((@Law3755.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3762 takes them (9 nodes). -/
def ordS8R9_Law3762 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3762. -/
theorem noS8R9_Law3762 : ∀ v : Magma.tup8R9,
    ¬ @Equation3762 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3762) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law3762) (by native_decide) v.1 v.2
    ((@Law3762.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3765 takes them (9 nodes). -/
def ordS8R9_Law3765 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3765. -/
theorem noS8R9_Law3765 : ∀ v : Magma.tup8R9,
    ¬ @Equation3765 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3765) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3765) (by native_decide) v.1 v.2
    ((@Law3765.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3769 takes them (44 nodes). -/
def ordS8R9_Law3769 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3769. -/
theorem noS8R9_Law3769 : ∀ v : Magma.tup8R9,
    ¬ @Equation3769 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3769) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3769) (by native_decide) v.1 v.2
    ((@Law3769.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3773 takes them (9 nodes). -/
def ordS8R9_Law3773 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3773. -/
theorem noS8R9_Law3773 : ∀ v : Magma.tup8R9,
    ¬ @Equation3773 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3773) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3773) (by native_decide) v.1 v.2
    ((@Law3773.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3777 takes them (9 nodes). -/
def ordS8R9_Law3777 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3777. -/
theorem noS8R9_Law3777 : ∀ v : Magma.tup8R9,
    ¬ @Equation3777 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3777) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3777) (by native_decide) v.1 v.2
    ((@Law3777.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3781 takes them (9 nodes). -/
def ordS8R9_Law3781 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3781. -/
theorem noS8R9_Law3781 : ∀ v : Magma.tup8R9,
    ¬ @Equation3781 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3781) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3781) (by native_decide) v.1 v.2
    ((@Law3781.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3794 takes them (9 nodes). -/
def ordS8R9_Law3794 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3794. -/
theorem noS8R9_Law3794 : ∀ v : Magma.tup8R9,
    ¬ @Equation3794 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3794) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3794) (by native_decide) v.1 v.2
    ((@Law3794.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3798 takes them (9 nodes). -/
def ordS8R9_Law3798 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3798. -/
theorem noS8R9_Law3798 : ∀ v : Magma.tup8R9,
    ¬ @Equation3798 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3798) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3798) (by native_decide) v.1 v.2
    ((@Law3798.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3807 takes them (9 nodes). -/
def ordS8R9_Law3807 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3807. -/
theorem noS8R9_Law3807 : ∀ v : Magma.tup8R9,
    ¬ @Equation3807 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3807) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3807) (by native_decide) v.1 v.2
    ((@Law3807.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3811 takes them (9 nodes). -/
def ordS8R9_Law3811 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3811. -/
theorem noS8R9_Law3811 : ∀ v : Magma.tup8R9,
    ¬ @Equation3811 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3811) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3811) (by native_decide) v.1 v.2
    ((@Law3811.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3815 takes them (9 nodes). -/
def ordS8R9_Law3815 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3815. -/
theorem noS8R9_Law3815 : ∀ v : Magma.tup8R9,
    ¬ @Equation3815 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3815) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3815) (by native_decide) v.1 v.2
    ((@Law3815.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3820 takes them (9 nodes). -/
def ordS8R9_Law3820 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3820. -/
theorem noS8R9_Law3820 : ∀ v : Magma.tup8R9,
    ¬ @Equation3820 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3820) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3820) (by native_decide) v.1 v.2
    ((@Law3820.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3824 takes them (9 nodes). -/
def ordS8R9_Law3824 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3824. -/
theorem noS8R9_Law3824 : ∀ v : Magma.tup8R9,
    ¬ @Equation3824 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3824) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3824) (by native_decide) v.1 v.2
    ((@Law3824.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3828 takes them (9 nodes). -/
def ordS8R9_Law3828 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3828. -/
theorem noS8R9_Law3828 : ∀ v : Magma.tup8R9,
    ¬ @Equation3828 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3828) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3828) (by native_decide) v.1 v.2
    ((@Law3828.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3832 takes them (9 nodes). -/
def ordS8R9_Law3832 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3832. -/
theorem noS8R9_Law3832 : ∀ v : Magma.tup8R9,
    ¬ @Equation3832 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3832) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3832) (by native_decide) v.1 v.2
    ((@Law3832.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3837 takes them (9 nodes). -/
def ordS8R9_Law3837 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3837. -/
theorem noS8R9_Law3837 : ∀ v : Magma.tup8R9,
    ¬ @Equation3837 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3837) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3837) (by native_decide) v.1 v.2
    ((@Law3837.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3842 takes them (9 nodes). -/
def ordS8R9_Law3842 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3842. -/
theorem noS8R9_Law3842 : ∀ v : Magma.tup8R9,
    ¬ @Equation3842 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3842) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3842) (by native_decide) v.1 v.2
    ((@Law3842.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3847 takes them (9 nodes). -/
def ordS8R9_Law3847 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3847. -/
theorem noS8R9_Law3847 : ∀ v : Magma.tup8R9,
    ¬ @Equation3847 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3847) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3847) (by native_decide) v.1 v.2
    ((@Law3847.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3852 takes them (9 nodes). -/
def ordS8R9_Law3852 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3852. -/
theorem noS8R9_Law3852 : ∀ v : Magma.tup8R9,
    ¬ @Equation3852 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3852) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3852) (by native_decide) v.1 v.2
    ((@Law3852.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3857 takes them (9 nodes). -/
def ordS8R9_Law3857 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3857. -/
theorem noS8R9_Law3857 : ∀ v : Magma.tup8R9,
    ¬ @Equation3857 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3857) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3857) (by native_decide) v.1 v.2
    ((@Law3857.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3866 takes them (741 nodes). -/
def ordS8R9_Law3866 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3866. -/
theorem noS8R9_Law3866 : ∀ v : Magma.tup8R9,
    ¬ @Equation3866 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3866) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3866) (by native_decide) v.1 v.2
    ((@Law3866.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3869 takes them (741 nodes). -/
def ordS8R9_Law3869 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3869. -/
theorem noS8R9_Law3869 : ∀ v : Magma.tup8R9,
    ¬ @Equation3869 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3869) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3869) (by native_decide) v.1 v.2
    ((@Law3869.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3872 takes them (9 nodes). -/
def ordS8R9_Law3872 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3872. -/
theorem noS8R9_Law3872 : ∀ v : Magma.tup8R9,
    ¬ @Equation3872 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3872) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3872) (by native_decide) v.1 v.2
    ((@Law3872.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3874 takes them (103 nodes). -/
def ordS8R9_Law3874 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3874. -/
theorem noS8R9_Law3874 : ∀ v : Magma.tup8R9,
    ¬ @Equation3874 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3874) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3874) (by native_decide) v.1 v.2
    ((@Law3874.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3875 takes them (31 nodes). -/
def ordS8R9_Law3875 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3875. -/
theorem noS8R9_Law3875 : ∀ v : Magma.tup8R9,
    ¬ @Equation3875 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3875) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3875) (by native_decide) v.1 v.2
    ((@Law3875.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3876 takes them (9 nodes). -/
def ordS8R9_Law3876 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3876. -/
theorem noS8R9_Law3876 : ∀ v : Magma.tup8R9,
    ¬ @Equation3876 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3876) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3876) (by native_decide) v.1 v.2
    ((@Law3876.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3893 takes them (776 nodes). -/
def ordS8R9_Law3893 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3893. -/
theorem noS8R9_Law3893 : ∀ v : Magma.tup8R9,
    ¬ @Equation3893 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3893) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3893) (by native_decide) v.1 v.2
    ((@Law3893.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `31` equations. -/
theorem srch8R9_refutes_212 :
    FamilyRefutes Magma.srch8R9 [
      3745, 3746, 3747, 3755, 3762, 3765, 3769, 3773, 3777, 3781, 3794, 3798, 3807, 3811, 3815,
      3820, 3824, 3828, 3832, 3837, 3842, 3847, 3852, 3857, 3866, 3869, 3872, 3874, 3875, 3876,
      3893
    ] :=
  ⟨noS8R9_Law3745, noS8R9_Law3746, noS8R9_Law3747, noS8R9_Law3755, noS8R9_Law3762, noS8R9_Law3765, noS8R9_Law3769, noS8R9_Law3773, noS8R9_Law3777, noS8R9_Law3781, noS8R9_Law3794, noS8R9_Law3798, noS8R9_Law3807, noS8R9_Law3811, noS8R9_Law3815, noS8R9_Law3820, noS8R9_Law3824, noS8R9_Law3828, noS8R9_Law3832, noS8R9_Law3837, noS8R9_Law3842, noS8R9_Law3847, noS8R9_Law3852, noS8R9_Law3857, noS8R9_Law3866, noS8R9_Law3869, noS8R9_Law3872, noS8R9_Law3874, noS8R9_Law3875, noS8R9_Law3876, noS8R9_Law3893⟩

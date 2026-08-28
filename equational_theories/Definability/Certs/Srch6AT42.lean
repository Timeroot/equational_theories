import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 43 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `36`
equations here, 2,449 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3835 takes them (103 nodes). -/
def ordS6A_Law3835 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3835. -/
theorem noS6A_Law3835 : ∀ v : Magma.tupS6A,
    ¬ @Equation3835 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3835) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3835) (by native_decide) v.1 v.2
    ((@Law3835.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3836 takes them (43 nodes). -/
def ordS6A_Law3836 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3836. -/
theorem noS6A_Law3836 : ∀ v : Magma.tupS6A,
    ¬ @Equation3836 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3836) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3836) (by native_decide) v.1 v.2
    ((@Law3836.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3838 takes them (32 nodes). -/
def ordS6A_Law3838 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3838. -/
theorem noS6A_Law3838 : ∀ v : Magma.tupS6A,
    ¬ @Equation3838 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3838) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3838) (by native_decide) v.1 v.2
    ((@Law3838.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3839 takes them (32 nodes). -/
def ordS6A_Law3839 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3839. -/
theorem noS6A_Law3839 : ∀ v : Magma.tupS6A,
    ¬ @Equation3839 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3839) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3839) (by native_decide) v.1 v.2
    ((@Law3839.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3840 takes them (32 nodes). -/
def ordS6A_Law3840 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3840. -/
theorem noS6A_Law3840 : ∀ v : Magma.tupS6A,
    ¬ @Equation3840 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3840) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3840) (by native_decide) v.1 v.2
    ((@Law3840.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3841 takes them (85 nodes). -/
def ordS6A_Law3841 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3841. -/
theorem noS6A_Law3841 : ∀ v : Magma.tupS6A,
    ¬ @Equation3841 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3841) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3841) (by native_decide) v.1 v.2
    ((@Law3841.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3842 takes them (187 nodes). -/
def ordS6A_Law3842 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3842. -/
theorem noS6A_Law3842 : ∀ v : Magma.tupS6A,
    ¬ @Equation3842 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3842) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3842) (by native_decide) v.1 v.2
    ((@Law3842.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3843 takes them (61 nodes). -/
def ordS6A_Law3843 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3843. -/
theorem noS6A_Law3843 : ∀ v : Magma.tupS6A,
    ¬ @Equation3843 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3843) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3843) (by native_decide) v.1 v.2
    ((@Law3843.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3844 takes them (67 nodes). -/
def ordS6A_Law3844 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3844. -/
theorem noS6A_Law3844 : ∀ v : Magma.tupS6A,
    ¬ @Equation3844 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3844) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3844) (by native_decide) v.1 v.2
    ((@Law3844.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3845 takes them (48 nodes). -/
def ordS6A_Law3845 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3845. -/
theorem noS6A_Law3845 : ∀ v : Magma.tupS6A,
    ¬ @Equation3845 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3845) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3845) (by native_decide) v.1 v.2
    ((@Law3845.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3846 takes them (33 nodes). -/
def ordS6A_Law3846 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3846. -/
theorem noS6A_Law3846 : ∀ v : Magma.tupS6A,
    ¬ @Equation3846 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3846) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3846) (by native_decide) v.1 v.2
    ((@Law3846.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3847 takes them (56 nodes). -/
def ordS6A_Law3847 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3847. -/
theorem noS6A_Law3847 : ∀ v : Magma.tupS6A,
    ¬ @Equation3847 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3847) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3847) (by native_decide) v.1 v.2
    ((@Law3847.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3848 takes them (39 nodes). -/
def ordS6A_Law3848 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3848. -/
theorem noS6A_Law3848 : ∀ v : Magma.tupS6A,
    ¬ @Equation3848 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3848) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3848) (by native_decide) v.1 v.2
    ((@Law3848.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3849 takes them (30 nodes). -/
def ordS6A_Law3849 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3849. -/
theorem noS6A_Law3849 : ∀ v : Magma.tupS6A,
    ¬ @Equation3849 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3849) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3849) (by native_decide) v.1 v.2
    ((@Law3849.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3850 takes them (30 nodes). -/
def ordS6A_Law3850 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3850. -/
theorem noS6A_Law3850 : ∀ v : Magma.tupS6A,
    ¬ @Equation3850 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3850) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3850) (by native_decide) v.1 v.2
    ((@Law3850.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3851 takes them (72 nodes). -/
def ordS6A_Law3851 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3851. -/
theorem noS6A_Law3851 : ∀ v : Magma.tupS6A,
    ¬ @Equation3851 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3851) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3851) (by native_decide) v.1 v.2
    ((@Law3851.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3852 takes them (87 nodes). -/
def ordS6A_Law3852 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3852. -/
theorem noS6A_Law3852 : ∀ v : Magma.tupS6A,
    ¬ @Equation3852 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3852) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3852) (by native_decide) v.1 v.2
    ((@Law3852.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3853 takes them (70 nodes). -/
def ordS6A_Law3853 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3853. -/
theorem noS6A_Law3853 : ∀ v : Magma.tupS6A,
    ¬ @Equation3853 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3853) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3853) (by native_decide) v.1 v.2
    ((@Law3853.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3854 takes them (88 nodes). -/
def ordS6A_Law3854 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3854. -/
theorem noS6A_Law3854 : ∀ v : Magma.tupS6A,
    ¬ @Equation3854 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3854) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3854) (by native_decide) v.1 v.2
    ((@Law3854.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3855 takes them (61 nodes). -/
def ordS6A_Law3855 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3855. -/
theorem noS6A_Law3855 : ∀ v : Magma.tupS6A,
    ¬ @Equation3855 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3855) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3855) (by native_decide) v.1 v.2
    ((@Law3855.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3856 takes them (32 nodes). -/
def ordS6A_Law3856 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3856. -/
theorem noS6A_Law3856 : ∀ v : Magma.tupS6A,
    ¬ @Equation3856 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3856) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3856) (by native_decide) v.1 v.2
    ((@Law3856.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3857 takes them (56 nodes). -/
def ordS6A_Law3857 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3857. -/
theorem noS6A_Law3857 : ∀ v : Magma.tupS6A,
    ¬ @Equation3857 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3857) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3857) (by native_decide) v.1 v.2
    ((@Law3857.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3858 takes them (30 nodes). -/
def ordS6A_Law3858 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3858. -/
theorem noS6A_Law3858 : ∀ v : Magma.tupS6A,
    ¬ @Equation3858 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3858) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3858) (by native_decide) v.1 v.2
    ((@Law3858.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3859 takes them (30 nodes). -/
def ordS6A_Law3859 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3859. -/
theorem noS6A_Law3859 : ∀ v : Magma.tupS6A,
    ¬ @Equation3859 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3859) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3859) (by native_decide) v.1 v.2
    ((@Law3859.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3860 takes them (30 nodes). -/
def ordS6A_Law3860 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3860. -/
theorem noS6A_Law3860 : ∀ v : Magma.tupS6A,
    ¬ @Equation3860 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3860) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3860) (by native_decide) v.1 v.2
    ((@Law3860.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3861 takes them (30 nodes). -/
def ordS6A_Law3861 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3861. -/
theorem noS6A_Law3861 : ∀ v : Magma.tupS6A,
    ¬ @Equation3861 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3861) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 6)
    (ord := ordS6A_Law3861) (by native_decide) v.1 v.2
    ((@Law3861.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3914 takes them (160 nodes). -/
def ordS6A_Law3914 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3914. -/
theorem noS6A_Law3914 : ∀ v : Magma.tupS6A,
    ¬ @Equation3914 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3914) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3914) (by native_decide) v.1 v.2
    ((@Law3914.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3916 takes them (148 nodes). -/
def ordS6A_Law3916 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3916. -/
theorem noS6A_Law3916 : ∀ v : Magma.tupS6A,
    ¬ @Equation3916 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3916) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3916) (by native_decide) v.1 v.2
    ((@Law3916.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3920 takes them (75 nodes). -/
def ordS6A_Law3920 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3920. -/
theorem noS6A_Law3920 : ∀ v : Magma.tupS6A,
    ¬ @Equation3920 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3920) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3920) (by native_decide) v.1 v.2
    ((@Law3920.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3922 takes them (61 nodes). -/
def ordS6A_Law3922 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3922. -/
theorem noS6A_Law3922 : ∀ v : Magma.tupS6A,
    ¬ @Equation3922 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3922) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3922) (by native_decide) v.1 v.2
    ((@Law3922.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3923 takes them (59 nodes). -/
def ordS6A_Law3923 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3923. -/
theorem noS6A_Law3923 : ∀ v : Magma.tupS6A,
    ¬ @Equation3923 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3923) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3923) (by native_decide) v.1 v.2
    ((@Law3923.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3932 takes them (218 nodes). -/
def ordS6A_Law3932 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3932. -/
theorem noS6A_Law3932 : ∀ v : Magma.tupS6A,
    ¬ @Equation3932 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3932) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3932) (by native_decide) v.1 v.2
    ((@Law3932.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3933 takes them (70 nodes). -/
def ordS6A_Law3933 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3933. -/
theorem noS6A_Law3933 : ∀ v : Magma.tupS6A,
    ¬ @Equation3933 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3933) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3933) (by native_decide) v.1 v.2
    ((@Law3933.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3934 takes them (84 nodes). -/
def ordS6A_Law3934 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3934. -/
theorem noS6A_Law3934 : ∀ v : Magma.tupS6A,
    ¬ @Equation3934 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3934) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3934) (by native_decide) v.1 v.2
    ((@Law3934.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3936 takes them (55 nodes). -/
def ordS6A_Law3936 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3936. -/
theorem noS6A_Law3936 : ∀ v : Magma.tupS6A,
    ¬ @Equation3936 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3936) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3936) (by native_decide) v.1 v.2
    ((@Law3936.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3937 takes them (55 nodes). -/
def ordS6A_Law3937 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3937. -/
theorem noS6A_Law3937 : ∀ v : Magma.tupS6A,
    ¬ @Equation3937 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3937) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3937) (by native_decide) v.1 v.2
    ((@Law3937.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `36` equations. -/
theorem srch6A_refutes_42 :
    FamilyRefutes Magma.srch6A [
      3835, 3836, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850,
      3851, 3852, 3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3914, 3916, 3920, 3922,
      3923, 3932, 3933, 3934, 3936, 3937
    ] :=
  ⟨noS6A_Law3835, noS6A_Law3836, noS6A_Law3838, noS6A_Law3839, noS6A_Law3840, noS6A_Law3841, noS6A_Law3842, noS6A_Law3843, noS6A_Law3844, noS6A_Law3845, noS6A_Law3846, noS6A_Law3847, noS6A_Law3848, noS6A_Law3849, noS6A_Law3850, noS6A_Law3851, noS6A_Law3852, noS6A_Law3853, noS6A_Law3854, noS6A_Law3855, noS6A_Law3856, noS6A_Law3857, noS6A_Law3858, noS6A_Law3859, noS6A_Law3860, noS6A_Law3861, noS6A_Law3914, noS6A_Law3916, noS6A_Law3920, noS6A_Law3922, noS6A_Law3923, noS6A_Law3932, noS6A_Law3933, noS6A_Law3934, noS6A_Law3936, noS6A_Law3937⟩

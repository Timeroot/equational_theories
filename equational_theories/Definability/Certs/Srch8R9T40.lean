import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 41 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `30`
equations here, 2,637 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 778 takes them (855 nodes). -/
def ordS8R9_Law778 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 778. -/
theorem noS8R9_Law778 : ∀ v : Magma.tup8R9,
    ¬ @Equation778 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law778) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law778) (by native_decide) v.1 v.2
    ((@Law778.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 782 takes them (73 nodes). -/
def ordS8R9_Law782 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 782. -/
theorem noS8R9_Law782 : ∀ v : Magma.tup8R9,
    ¬ @Equation782 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law782) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law782) (by native_decide) v.1 v.2
    ((@Law782.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 786 takes them (15 nodes). -/
def ordS8R9_Law786 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 786. -/
theorem noS8R9_Law786 : ∀ v : Magma.tup8R9,
    ¬ @Equation786 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law786) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law786) (by native_decide) v.1 v.2
    ((@Law786.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 791 takes them (741 nodes). -/
def ordS8R9_Law791 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 791. -/
theorem noS8R9_Law791 : ∀ v : Magma.tup8R9,
    ¬ @Equation791 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law791) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law791) (by native_decide) v.1 v.2
    ((@Law791.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 796 takes them (358 nodes). -/
def ordS8R9_Law796 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 796. -/
theorem noS8R9_Law796 : ∀ v : Magma.tup8R9,
    ¬ @Equation796 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law796) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law796) (by native_decide) v.1 v.2
    ((@Law796.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 801 takes them (13 nodes). -/
def ordS8R9_Law801 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 801. -/
theorem noS8R9_Law801 : ∀ v : Magma.tup8R9,
    ¬ @Equation801 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law801) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law801) (by native_decide) v.1 v.2
    ((@Law801.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 806 takes them (9 nodes). -/
def ordS8R9_Law806 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 806. -/
theorem noS8R9_Law806 : ∀ v : Magma.tup8R9,
    ¬ @Equation806 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law806) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law806) (by native_decide) v.1 v.2
    ((@Law806.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 811 takes them (12 nodes). -/
def ordS8R9_Law811 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 811. -/
theorem noS8R9_Law811 : ∀ v : Magma.tup8R9,
    ¬ @Equation811 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law811) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law811) (by native_decide) v.1 v.2
    ((@Law811.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 840 takes them (62 nodes). -/
def ordS8R9_Law840 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 840. -/
theorem noS8R9_Law840 : ∀ v : Magma.tup8R9,
    ¬ @Equation840 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law840) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law840) (by native_decide) v.1 v.2
    ((@Law840.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 841 takes them (62 nodes). -/
def ordS8R9_Law841 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 841. -/
theorem noS8R9_Law841 : ∀ v : Magma.tup8R9,
    ¬ @Equation841 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law841) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law841) (by native_decide) v.1 v.2
    ((@Law841.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 844 takes them (64 nodes). -/
def ordS8R9_Law844 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 844. -/
theorem noS8R9_Law844 : ∀ v : Magma.tup8R9,
    ¬ @Equation844 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law844) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law844) (by native_decide) v.1 v.2
    ((@Law844.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 846 takes them (9 nodes). -/
def ordS8R9_Law846 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 846. -/
theorem noS8R9_Law846 : ∀ v : Magma.tup8R9,
    ¬ @Equation846 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law846) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law846) (by native_decide) v.1 v.2
    ((@Law846.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 847 takes them (9 nodes). -/
def ordS8R9_Law847 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 847. -/
theorem noS8R9_Law847 : ∀ v : Magma.tup8R9,
    ¬ @Equation847 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law847) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law847) (by native_decide) v.1 v.2
    ((@Law847.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 849 takes them (9 nodes). -/
def ordS8R9_Law849 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 849. -/
theorem noS8R9_Law849 : ∀ v : Magma.tup8R9,
    ¬ @Equation849 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law849) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law849) (by native_decide) v.1 v.2
    ((@Law849.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 850 takes them (9 nodes). -/
def ordS8R9_Law850 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 850. -/
theorem noS8R9_Law850 : ∀ v : Magma.tup8R9,
    ¬ @Equation850 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law850) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law850) (by native_decide) v.1 v.2
    ((@Law850.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 851 takes them (9 nodes). -/
def ordS8R9_Law851 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 851. -/
theorem noS8R9_Law851 : ∀ v : Magma.tup8R9,
    ¬ @Equation851 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law851) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law851) (by native_decide) v.1 v.2
    ((@Law851.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 853 takes them (154 nodes). -/
def ordS8R9_Law853 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 853. -/
theorem noS8R9_Law853 : ∀ v : Magma.tup8R9,
    ¬ @Equation853 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law853) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law853) (by native_decide) v.1 v.2
    ((@Law853.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 855 takes them (64 nodes). -/
def ordS8R9_Law855 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 855. -/
theorem noS8R9_Law855 : ∀ v : Magma.tup8R9,
    ¬ @Equation855 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law855) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law855) (by native_decide) v.1 v.2
    ((@Law855.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 857 takes them (9 nodes). -/
def ordS8R9_Law857 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 857. -/
theorem noS8R9_Law857 : ∀ v : Magma.tup8R9,
    ¬ @Equation857 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law857) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law857) (by native_decide) v.1 v.2
    ((@Law857.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 858 takes them (9 nodes). -/
def ordS8R9_Law858 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 858. -/
theorem noS8R9_Law858 : ∀ v : Magma.tup8R9,
    ¬ @Equation858 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law858) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law858) (by native_decide) v.1 v.2
    ((@Law858.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 859 takes them (9 nodes). -/
def ordS8R9_Law859 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 859. -/
theorem noS8R9_Law859 : ∀ v : Magma.tup8R9,
    ¬ @Equation859 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law859) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law859) (by native_decide) v.1 v.2
    ((@Law859.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 861 takes them (9 nodes). -/
def ordS8R9_Law861 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 861. -/
theorem noS8R9_Law861 : ∀ v : Magma.tup8R9,
    ¬ @Equation861 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law861) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law861) (by native_decide) v.1 v.2
    ((@Law861.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 862 takes them (9 nodes). -/
def ordS8R9_Law862 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 862. -/
theorem noS8R9_Law862 : ∀ v : Magma.tup8R9,
    ¬ @Equation862 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law862) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law862) (by native_decide) v.1 v.2
    ((@Law862.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 863 takes them (9 nodes). -/
def ordS8R9_Law863 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 863. -/
theorem noS8R9_Law863 : ∀ v : Magma.tup8R9,
    ¬ @Equation863 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law863) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law863) (by native_decide) v.1 v.2
    ((@Law863.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 865 takes them (9 nodes). -/
def ordS8R9_Law865 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 865. -/
theorem noS8R9_Law865 : ∀ v : Magma.tup8R9,
    ¬ @Equation865 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law865) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law865) (by native_decide) v.1 v.2
    ((@Law865.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 866 takes them (9 nodes). -/
def ordS8R9_Law866 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 866. -/
theorem noS8R9_Law866 : ∀ v : Magma.tup8R9,
    ¬ @Equation866 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law866) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law866) (by native_decide) v.1 v.2
    ((@Law866.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 867 takes them (9 nodes). -/
def ordS8R9_Law867 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 867. -/
theorem noS8R9_Law867 : ∀ v : Magma.tup8R9,
    ¬ @Equation867 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law867) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law867) (by native_decide) v.1 v.2
    ((@Law867.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 868 takes them (11 nodes). -/
def ordS8R9_Law868 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 868. -/
theorem noS8R9_Law868 : ∀ v : Magma.tup8R9,
    ¬ @Equation868 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law868) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law868) (by native_decide) v.1 v.2
    ((@Law868.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 869 takes them (9 nodes). -/
def ordS8R9_Law869 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 869. -/
theorem noS8R9_Law869 : ∀ v : Magma.tup8R9,
    ¬ @Equation869 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law869) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law869) (by native_decide) v.1 v.2
    ((@Law869.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 875 takes them (9 nodes). -/
def ordS8R9_Law875 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 875. -/
theorem noS8R9_Law875 : ∀ v : Magma.tup8R9,
    ¬ @Equation875 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law875) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law875) (by native_decide) v.1 v.2
    ((@Law875.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `30` equations. -/
theorem srch8R9_refutes_40 :
    FamilyRefutes Magma.srch8R9 [
      778, 782, 786, 791, 796, 801, 806, 811, 840, 841, 844, 846, 847, 849, 850, 851, 853, 855,
      857, 858, 859, 861, 862, 863, 865, 866, 867, 868, 869, 875
    ] :=
  ⟨noS8R9_Law778, noS8R9_Law782, noS8R9_Law786, noS8R9_Law791, noS8R9_Law796, noS8R9_Law801, noS8R9_Law806, noS8R9_Law811, noS8R9_Law840, noS8R9_Law841, noS8R9_Law844, noS8R9_Law846, noS8R9_Law847, noS8R9_Law849, noS8R9_Law850, noS8R9_Law851, noS8R9_Law853, noS8R9_Law855, noS8R9_Law857, noS8R9_Law858, noS8R9_Law859, noS8R9_Law861, noS8R9_Law862, noS8R9_Law863, noS8R9_Law865, noS8R9_Law866, noS8R9_Law867, noS8R9_Law868, noS8R9_Law869, noS8R9_Law875⟩

import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 10 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `79` equations here, 840 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3857 takes them (10 nodes). -/
def ordS8R164_Law3857 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3857. -/
theorem noS8R164_Law3857 : ∀ v : Magma.tup8R164,
    ¬ @Equation3857 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3857) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3857) (by native_decide) v.1 v.2
    ((@Law3857.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3858 takes them (6 nodes). -/
def ordS8R164_Law3858 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3858. -/
theorem noS8R164_Law3858 : ∀ v : Magma.tup8R164,
    ¬ @Equation3858 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3858) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3858) (by native_decide) v.1 v.2
    ((@Law3858.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3859 takes them (6 nodes). -/
def ordS8R164_Law3859 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3859. -/
theorem noS8R164_Law3859 : ∀ v : Magma.tup8R164,
    ¬ @Equation3859 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3859) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3859) (by native_decide) v.1 v.2
    ((@Law3859.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3860 takes them (6 nodes). -/
def ordS8R164_Law3860 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3860. -/
theorem noS8R164_Law3860 : ∀ v : Magma.tup8R164,
    ¬ @Equation3860 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3860) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3860) (by native_decide) v.1 v.2
    ((@Law3860.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3861 takes them (6 nodes). -/
def ordS8R164_Law3861 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3861. -/
theorem noS8R164_Law3861 : ∀ v : Magma.tup8R164,
    ¬ @Equation3861 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3861) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law3861) (by native_decide) v.1 v.2
    ((@Law3861.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3864 takes them (21 nodes). -/
def ordS8R164_Law3864 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3864. -/
theorem noS8R164_Law3864 : ∀ v : Magma.tup8R164,
    ¬ @Equation3864 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3864) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3864) (by native_decide) v.1 v.2
    ((@Law3864.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3866 takes them (10 nodes). -/
def ordS8R164_Law3866 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3866. -/
theorem noS8R164_Law3866 : ∀ v : Magma.tup8R164,
    ¬ @Equation3866 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3866) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3866) (by native_decide) v.1 v.2
    ((@Law3866.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3867 takes them (23 nodes). -/
def ordS8R164_Law3867 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3867. -/
theorem noS8R164_Law3867 : ∀ v : Magma.tup8R164,
    ¬ @Equation3867 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3867) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3867) (by native_decide) v.1 v.2
    ((@Law3867.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3869 takes them (10 nodes). -/
def ordS8R164_Law3869 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3869. -/
theorem noS8R164_Law3869 : ∀ v : Magma.tup8R164,
    ¬ @Equation3869 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3869) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3869) (by native_decide) v.1 v.2
    ((@Law3869.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3873 takes them (20 nodes). -/
def ordS8R164_Law3873 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3873. -/
theorem noS8R164_Law3873 : ∀ v : Magma.tup8R164,
    ¬ @Equation3873 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3873) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3873) (by native_decide) v.1 v.2
    ((@Law3873.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3874 takes them (10 nodes). -/
def ordS8R164_Law3874 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3874. -/
theorem noS8R164_Law3874 : ∀ v : Magma.tup8R164,
    ¬ @Equation3874 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3874) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3874) (by native_decide) v.1 v.2
    ((@Law3874.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3875 takes them (12 nodes). -/
def ordS8R164_Law3875 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3875. -/
theorem noS8R164_Law3875 : ∀ v : Magma.tup8R164,
    ¬ @Equation3875 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3875) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3875) (by native_decide) v.1 v.2
    ((@Law3875.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3876 takes them (9 nodes). -/
def ordS8R164_Law3876 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3876. -/
theorem noS8R164_Law3876 : ∀ v : Magma.tup8R164,
    ¬ @Equation3876 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3876) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3876) (by native_decide) v.1 v.2
    ((@Law3876.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3881 takes them (16 nodes). -/
def ordS8R164_Law3881 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3881. -/
theorem noS8R164_Law3881 : ∀ v : Magma.tup8R164,
    ¬ @Equation3881 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3881) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3881) (by native_decide) v.1 v.2
    ((@Law3881.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3882 takes them (7 nodes). -/
def ordS8R164_Law3882 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3882. -/
theorem noS8R164_Law3882 : ∀ v : Magma.tup8R164,
    ¬ @Equation3882 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3882) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3882) (by native_decide) v.1 v.2
    ((@Law3882.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3883 takes them (11 nodes). -/
def ordS8R164_Law3883 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3883. -/
theorem noS8R164_Law3883 : ∀ v : Magma.tup8R164,
    ¬ @Equation3883 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3883) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3883) (by native_decide) v.1 v.2
    ((@Law3883.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3884 takes them (12 nodes). -/
def ordS8R164_Law3884 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3884. -/
theorem noS8R164_Law3884 : ∀ v : Magma.tup8R164,
    ¬ @Equation3884 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3884) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3884) (by native_decide) v.1 v.2
    ((@Law3884.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3885 takes them (9 nodes). -/
def ordS8R164_Law3885 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3885. -/
theorem noS8R164_Law3885 : ∀ v : Magma.tup8R164,
    ¬ @Equation3885 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3885) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3885) (by native_decide) v.1 v.2
    ((@Law3885.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3886 takes them (6 nodes). -/
def ordS8R164_Law3886 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3886. -/
theorem noS8R164_Law3886 : ∀ v : Magma.tup8R164,
    ¬ @Equation3886 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3886) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3886) (by native_decide) v.1 v.2
    ((@Law3886.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3888 takes them (13 nodes). -/
def ordS8R164_Law3888 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3888. -/
theorem noS8R164_Law3888 : ∀ v : Magma.tup8R164,
    ¬ @Equation3888 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3888) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3888) (by native_decide) v.1 v.2
    ((@Law3888.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3889 takes them (8 nodes). -/
def ordS8R164_Law3889 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3889. -/
theorem noS8R164_Law3889 : ∀ v : Magma.tup8R164,
    ¬ @Equation3889 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3889) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3889) (by native_decide) v.1 v.2
    ((@Law3889.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3893 takes them (12 nodes). -/
def ordS8R164_Law3893 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3893. -/
theorem noS8R164_Law3893 : ∀ v : Magma.tup8R164,
    ¬ @Equation3893 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3893) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3893) (by native_decide) v.1 v.2
    ((@Law3893.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3894 takes them (12 nodes). -/
def ordS8R164_Law3894 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3894. -/
theorem noS8R164_Law3894 : ∀ v : Magma.tup8R164,
    ¬ @Equation3894 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3894) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3894) (by native_decide) v.1 v.2
    ((@Law3894.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3896 takes them (8 nodes). -/
def ordS8R164_Law3896 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3896. -/
theorem noS8R164_Law3896 : ∀ v : Magma.tup8R164,
    ¬ @Equation3896 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3896) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3896) (by native_decide) v.1 v.2
    ((@Law3896.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3897 takes them (12 nodes). -/
def ordS8R164_Law3897 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3897. -/
theorem noS8R164_Law3897 : ∀ v : Magma.tup8R164,
    ¬ @Equation3897 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3897) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3897) (by native_decide) v.1 v.2
    ((@Law3897.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3898 takes them (12 nodes). -/
def ordS8R164_Law3898 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3898. -/
theorem noS8R164_Law3898 : ∀ v : Magma.tup8R164,
    ¬ @Equation3898 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3898) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3898) (by native_decide) v.1 v.2
    ((@Law3898.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3899 takes them (7 nodes). -/
def ordS8R164_Law3899 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3899. -/
theorem noS8R164_Law3899 : ∀ v : Magma.tup8R164,
    ¬ @Equation3899 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3899) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3899) (by native_decide) v.1 v.2
    ((@Law3899.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3900 takes them (6 nodes). -/
def ordS8R164_Law3900 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3900. -/
theorem noS8R164_Law3900 : ∀ v : Magma.tup8R164,
    ¬ @Equation3900 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3900) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3900) (by native_decide) v.1 v.2
    ((@Law3900.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3901 takes them (11 nodes). -/
def ordS8R164_Law3901 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3901. -/
theorem noS8R164_Law3901 : ∀ v : Magma.tup8R164,
    ¬ @Equation3901 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3901) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3901) (by native_decide) v.1 v.2
    ((@Law3901.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3902 takes them (15 nodes). -/
def ordS8R164_Law3902 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3902. -/
theorem noS8R164_Law3902 : ∀ v : Magma.tup8R164,
    ¬ @Equation3902 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3902) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3902) (by native_decide) v.1 v.2
    ((@Law3902.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3904 takes them (7 nodes). -/
def ordS8R164_Law3904 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3904. -/
theorem noS8R164_Law3904 : ∀ v : Magma.tup8R164,
    ¬ @Equation3904 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3904) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3904) (by native_decide) v.1 v.2
    ((@Law3904.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3909 takes them (10 nodes). -/
def ordS8R164_Law3909 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3909. -/
theorem noS8R164_Law3909 : ∀ v : Magma.tup8R164,
    ¬ @Equation3909 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3909) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3909) (by native_decide) v.1 v.2
    ((@Law3909.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3910 takes them (12 nodes). -/
def ordS8R164_Law3910 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3910. -/
theorem noS8R164_Law3910 : ∀ v : Magma.tup8R164,
    ¬ @Equation3910 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3910) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3910) (by native_decide) v.1 v.2
    ((@Law3910.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3911 takes them (7 nodes). -/
def ordS8R164_Law3911 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3911. -/
theorem noS8R164_Law3911 : ∀ v : Magma.tup8R164,
    ¬ @Equation3911 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3911) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3911) (by native_decide) v.1 v.2
    ((@Law3911.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3912 takes them (9 nodes). -/
def ordS8R164_Law3912 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3912. -/
theorem noS8R164_Law3912 : ∀ v : Magma.tup8R164,
    ¬ @Equation3912 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3912) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3912) (by native_decide) v.1 v.2
    ((@Law3912.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3913 takes them (6 nodes). -/
def ordS8R164_Law3913 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3913. -/
theorem noS8R164_Law3913 : ∀ v : Magma.tup8R164,
    ¬ @Equation3913 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3913) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3913) (by native_decide) v.1 v.2
    ((@Law3913.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3914 takes them (9 nodes). -/
def ordS8R164_Law3914 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3914. -/
theorem noS8R164_Law3914 : ∀ v : Magma.tup8R164,
    ¬ @Equation3914 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3914) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3914) (by native_decide) v.1 v.2
    ((@Law3914.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3916 takes them (9 nodes). -/
def ordS8R164_Law3916 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3916. -/
theorem noS8R164_Law3916 : ∀ v : Magma.tup8R164,
    ¬ @Equation3916 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3916) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3916) (by native_decide) v.1 v.2
    ((@Law3916.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3918 takes them (25 nodes). -/
def ordS8R164_Law3918 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3918. -/
theorem noS8R164_Law3918 : ∀ v : Magma.tup8R164,
    ¬ @Equation3918 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3918) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3918) (by native_decide) v.1 v.2
    ((@Law3918.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3919 takes them (9 nodes). -/
def ordS8R164_Law3919 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3919. -/
theorem noS8R164_Law3919 : ∀ v : Magma.tup8R164,
    ¬ @Equation3919 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3919) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3919) (by native_decide) v.1 v.2
    ((@Law3919.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3920 takes them (9 nodes). -/
def ordS8R164_Law3920 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3920. -/
theorem noS8R164_Law3920 : ∀ v : Magma.tup8R164,
    ¬ @Equation3920 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3920) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3920) (by native_decide) v.1 v.2
    ((@Law3920.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3921 takes them (14 nodes). -/
def ordS8R164_Law3921 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3921. -/
theorem noS8R164_Law3921 : ∀ v : Magma.tup8R164,
    ¬ @Equation3921 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3921) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3921) (by native_decide) v.1 v.2
    ((@Law3921.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3922 takes them (9 nodes). -/
def ordS8R164_Law3922 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3922. -/
theorem noS8R164_Law3922 : ∀ v : Magma.tup8R164,
    ¬ @Equation3922 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3922) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3922) (by native_decide) v.1 v.2
    ((@Law3922.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3923 takes them (9 nodes). -/
def ordS8R164_Law3923 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3923. -/
theorem noS8R164_Law3923 : ∀ v : Magma.tup8R164,
    ¬ @Equation3923 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3923) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3923) (by native_decide) v.1 v.2
    ((@Law3923.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3925 takes them (29 nodes). -/
def ordS8R164_Law3925 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3925. -/
theorem noS8R164_Law3925 : ∀ v : Magma.tup8R164,
    ¬ @Equation3925 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3925) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3925) (by native_decide) v.1 v.2
    ((@Law3925.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3926 takes them (9 nodes). -/
def ordS8R164_Law3926 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3926. -/
theorem noS8R164_Law3926 : ∀ v : Magma.tup8R164,
    ¬ @Equation3926 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3926) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3926) (by native_decide) v.1 v.2
    ((@Law3926.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (17 nodes). -/
def ordS8R164_Law3927 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3927. -/
theorem noS8R164_Law3927 : ∀ v : Magma.tup8R164,
    ¬ @Equation3927 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3929 takes them (9 nodes). -/
def ordS8R164_Law3929 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3929. -/
theorem noS8R164_Law3929 : ∀ v : Magma.tup8R164,
    ¬ @Equation3929 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3929) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3929) (by native_decide) v.1 v.2
    ((@Law3929.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3930 takes them (10 nodes). -/
def ordS8R164_Law3930 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3930. -/
theorem noS8R164_Law3930 : ∀ v : Magma.tup8R164,
    ¬ @Equation3930 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3930) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3930) (by native_decide) v.1 v.2
    ((@Law3930.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (18 nodes). -/
def ordS8R164_Law3931 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3931. -/
theorem noS8R164_Law3931 : ∀ v : Magma.tup8R164,
    ¬ @Equation3931 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3933 takes them (9 nodes). -/
def ordS8R164_Law3933 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3933. -/
theorem noS8R164_Law3933 : ∀ v : Magma.tup8R164,
    ¬ @Equation3933 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3933) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3933) (by native_decide) v.1 v.2
    ((@Law3933.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3934 takes them (9 nodes). -/
def ordS8R164_Law3934 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3934. -/
theorem noS8R164_Law3934 : ∀ v : Magma.tup8R164,
    ¬ @Equation3934 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3934) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3934) (by native_decide) v.1 v.2
    ((@Law3934.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3935 takes them (19 nodes). -/
def ordS8R164_Law3935 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3935. -/
theorem noS8R164_Law3935 : ∀ v : Magma.tup8R164,
    ¬ @Equation3935 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3935) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3935) (by native_decide) v.1 v.2
    ((@Law3935.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3936 takes them (9 nodes). -/
def ordS8R164_Law3936 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3936. -/
theorem noS8R164_Law3936 : ∀ v : Magma.tup8R164,
    ¬ @Equation3936 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3936) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3936) (by native_decide) v.1 v.2
    ((@Law3936.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3937 takes them (9 nodes). -/
def ordS8R164_Law3937 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3937. -/
theorem noS8R164_Law3937 : ∀ v : Magma.tup8R164,
    ¬ @Equation3937 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3937) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3937) (by native_decide) v.1 v.2
    ((@Law3937.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3938 takes them (10 nodes). -/
def ordS8R164_Law3938 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3938. -/
theorem noS8R164_Law3938 : ∀ v : Magma.tup8R164,
    ¬ @Equation3938 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3938) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3938) (by native_decide) v.1 v.2
    ((@Law3938.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3939 takes them (13 nodes). -/
def ordS8R164_Law3939 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3939. -/
theorem noS8R164_Law3939 : ∀ v : Magma.tup8R164,
    ¬ @Equation3939 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3939) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3939) (by native_decide) v.1 v.2
    ((@Law3939.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3941 takes them (9 nodes). -/
def ordS8R164_Law3941 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3941. -/
theorem noS8R164_Law3941 : ∀ v : Magma.tup8R164,
    ¬ @Equation3941 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3941) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3941) (by native_decide) v.1 v.2
    ((@Law3941.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3942 takes them (9 nodes). -/
def ordS8R164_Law3942 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3942. -/
theorem noS8R164_Law3942 : ∀ v : Magma.tup8R164,
    ¬ @Equation3942 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3942) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3942) (by native_decide) v.1 v.2
    ((@Law3942.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3944 takes them (9 nodes). -/
def ordS8R164_Law3944 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3944. -/
theorem noS8R164_Law3944 : ∀ v : Magma.tup8R164,
    ¬ @Equation3944 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3944) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3944) (by native_decide) v.1 v.2
    ((@Law3944.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3945 takes them (9 nodes). -/
def ordS8R164_Law3945 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3945. -/
theorem noS8R164_Law3945 : ∀ v : Magma.tup8R164,
    ¬ @Equation3945 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3945) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3945) (by native_decide) v.1 v.2
    ((@Law3945.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3946 takes them (9 nodes). -/
def ordS8R164_Law3946 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3946. -/
theorem noS8R164_Law3946 : ∀ v : Magma.tup8R164,
    ¬ @Equation3946 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3946) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3946) (by native_decide) v.1 v.2
    ((@Law3946.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (13 nodes). -/
def ordS8R164_Law3947 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3947. -/
theorem noS8R164_Law3947 : ∀ v : Magma.tup8R164,
    ¬ @Equation3947 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3948 takes them (9 nodes). -/
def ordS8R164_Law3948 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3948. -/
theorem noS8R164_Law3948 : ∀ v : Magma.tup8R164,
    ¬ @Equation3948 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3948) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3948) (by native_decide) v.1 v.2
    ((@Law3948.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3949 takes them (9 nodes). -/
def ordS8R164_Law3949 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3949. -/
theorem noS8R164_Law3949 : ∀ v : Magma.tup8R164,
    ¬ @Equation3949 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3949) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3949) (by native_decide) v.1 v.2
    ((@Law3949.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3950 takes them (9 nodes). -/
def ordS8R164_Law3950 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3950. -/
theorem noS8R164_Law3950 : ∀ v : Magma.tup8R164,
    ¬ @Equation3950 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3950) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3950) (by native_decide) v.1 v.2
    ((@Law3950.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (17 nodes). -/
def ordS8R164_Law3952 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3952. -/
theorem noS8R164_Law3952 : ∀ v : Magma.tup8R164,
    ¬ @Equation3952 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3953 takes them (6 nodes). -/
def ordS8R164_Law3953 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3953. -/
theorem noS8R164_Law3953 : ∀ v : Magma.tup8R164,
    ¬ @Equation3953 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3953) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3953) (by native_decide) v.1 v.2
    ((@Law3953.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3954 takes them (12 nodes). -/
def ordS8R164_Law3954 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3954. -/
theorem noS8R164_Law3954 : ∀ v : Magma.tup8R164,
    ¬ @Equation3954 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3954) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3954) (by native_decide) v.1 v.2
    ((@Law3954.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3956 takes them (6 nodes). -/
def ordS8R164_Law3956 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3956. -/
theorem noS8R164_Law3956 : ∀ v : Magma.tup8R164,
    ¬ @Equation3956 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3956) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3956) (by native_decide) v.1 v.2
    ((@Law3956.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3957 takes them (7 nodes). -/
def ordS8R164_Law3957 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3957. -/
theorem noS8R164_Law3957 : ∀ v : Magma.tup8R164,
    ¬ @Equation3957 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3957) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3957) (by native_decide) v.1 v.2
    ((@Law3957.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3958 takes them (10 nodes). -/
def ordS8R164_Law3958 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3958. -/
theorem noS8R164_Law3958 : ∀ v : Magma.tup8R164,
    ¬ @Equation3958 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3958) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3958) (by native_decide) v.1 v.2
    ((@Law3958.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3960 takes them (6 nodes). -/
def ordS8R164_Law3960 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3960. -/
theorem noS8R164_Law3960 : ∀ v : Magma.tup8R164,
    ¬ @Equation3960 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3960) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3960) (by native_decide) v.1 v.2
    ((@Law3960.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3961 takes them (12 nodes). -/
def ordS8R164_Law3961 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3961. -/
theorem noS8R164_Law3961 : ∀ v : Magma.tup8R164,
    ¬ @Equation3961 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3961) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3961) (by native_decide) v.1 v.2
    ((@Law3961.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3963 takes them (6 nodes). -/
def ordS8R164_Law3963 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3963. -/
theorem noS8R164_Law3963 : ∀ v : Magma.tup8R164,
    ¬ @Equation3963 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3963) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3963) (by native_decide) v.1 v.2
    ((@Law3963.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3965 takes them (10 nodes). -/
def ordS8R164_Law3965 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3965. -/
theorem noS8R164_Law3965 : ∀ v : Magma.tup8R164,
    ¬ @Equation3965 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3965) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3965) (by native_decide) v.1 v.2
    ((@Law3965.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3966 takes them (6 nodes). -/
def ordS8R164_Law3966 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3966. -/
theorem noS8R164_Law3966 : ∀ v : Magma.tup8R164,
    ¬ @Equation3966 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3966) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3966) (by native_decide) v.1 v.2
    ((@Law3966.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3967 takes them (7 nodes). -/
def ordS8R164_Law3967 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3967. -/
theorem noS8R164_Law3967 : ∀ v : Magma.tup8R164,
    ¬ @Equation3967 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3967) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3967) (by native_decide) v.1 v.2
    ((@Law3967.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3968 takes them (10 nodes). -/
def ordS8R164_Law3968 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3968. -/
theorem noS8R164_Law3968 : ∀ v : Magma.tup8R164,
    ¬ @Equation3968 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3968) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3968) (by native_decide) v.1 v.2
    ((@Law3968.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `79` equations. -/
theorem srch8R164_refutes_9 :
    FamilyRefutes Magma.srch8R164 [
      3857, 3858, 3859, 3860, 3861, 3864, 3866, 3867, 3869, 3873, 3874, 3875, 3876, 3881, 3882,
      3883, 3884, 3885, 3886, 3888, 3889, 3893, 3894, 3896, 3897, 3898, 3899, 3900, 3901, 3902,
      3904, 3909, 3910, 3911, 3912, 3913, 3914, 3916, 3918, 3919, 3920, 3921, 3922, 3923, 3925,
      3926, 3927, 3929, 3930, 3931, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3941, 3942, 3944,
      3945, 3946, 3947, 3948, 3949, 3950, 3952, 3953, 3954, 3956, 3957, 3958, 3960, 3961, 3963,
      3965, 3966, 3967, 3968
    ] :=
  ⟨noS8R164_Law3857, noS8R164_Law3858, noS8R164_Law3859, noS8R164_Law3860, noS8R164_Law3861, noS8R164_Law3864, noS8R164_Law3866, noS8R164_Law3867, noS8R164_Law3869, noS8R164_Law3873, noS8R164_Law3874, noS8R164_Law3875, noS8R164_Law3876, noS8R164_Law3881, noS8R164_Law3882, noS8R164_Law3883, noS8R164_Law3884, noS8R164_Law3885, noS8R164_Law3886, noS8R164_Law3888, noS8R164_Law3889, noS8R164_Law3893, noS8R164_Law3894, noS8R164_Law3896, noS8R164_Law3897, noS8R164_Law3898, noS8R164_Law3899, noS8R164_Law3900, noS8R164_Law3901, noS8R164_Law3902, noS8R164_Law3904, noS8R164_Law3909, noS8R164_Law3910, noS8R164_Law3911, noS8R164_Law3912, noS8R164_Law3913, noS8R164_Law3914, noS8R164_Law3916, noS8R164_Law3918, noS8R164_Law3919, noS8R164_Law3920, noS8R164_Law3921, noS8R164_Law3922, noS8R164_Law3923, noS8R164_Law3925, noS8R164_Law3926, noS8R164_Law3927, noS8R164_Law3929, noS8R164_Law3930, noS8R164_Law3931, noS8R164_Law3933, noS8R164_Law3934, noS8R164_Law3935, noS8R164_Law3936, noS8R164_Law3937, noS8R164_Law3938, noS8R164_Law3939, noS8R164_Law3941, noS8R164_Law3942, noS8R164_Law3944, noS8R164_Law3945, noS8R164_Law3946, noS8R164_Law3947, noS8R164_Law3948, noS8R164_Law3949, noS8R164_Law3950, noS8R164_Law3952, noS8R164_Law3953, noS8R164_Law3954, noS8R164_Law3956, noS8R164_Law3957, noS8R164_Law3958, noS8R164_Law3960, noS8R164_Law3961, noS8R164_Law3963, noS8R164_Law3965, noS8R164_Law3966, noS8R164_Law3967, noS8R164_Law3968⟩

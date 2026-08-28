import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 28 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `22`
equations here, 2,775 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2867 takes them (85 nodes). -/
def ordS6A_Law2867 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2867. -/
theorem noS6A_Law2867 : ∀ v : Magma.tupS6A,
    ¬ @Equation2867 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2867) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2867) (by native_decide) v.1 v.2
    ((@Law2867.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2869 takes them (103 nodes). -/
def ordS6A_Law2869 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2869. -/
theorem noS6A_Law2869 : ∀ v : Magma.tupS6A,
    ¬ @Equation2869 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2869) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2869) (by native_decide) v.1 v.2
    ((@Law2869.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2870 takes them (204 nodes). -/
def ordS6A_Law2870 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2870. -/
theorem noS6A_Law2870 : ∀ v : Magma.tupS6A,
    ¬ @Equation2870 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2870) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2870) (by native_decide) v.1 v.2
    ((@Law2870.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2871 takes them (36 nodes). -/
def ordS6A_Law2871 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2871. -/
theorem noS6A_Law2871 : ∀ v : Magma.tupS6A,
    ¬ @Equation2871 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2871) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2871) (by native_decide) v.1 v.2
    ((@Law2871.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2873 takes them (392 nodes). -/
def ordS6A_Law2873 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2873. -/
theorem noS6A_Law2873 : ∀ v : Magma.tupS6A,
    ¬ @Equation2873 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2873) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2873) (by native_decide) v.1 v.2
    ((@Law2873.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2874 takes them (105 nodes). -/
def ordS6A_Law2874 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2874. -/
theorem noS6A_Law2874 : ∀ v : Magma.tupS6A,
    ¬ @Equation2874 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2874) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2874) (by native_decide) v.1 v.2
    ((@Law2874.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2877 takes them (78 nodes). -/
def ordS6A_Law2877 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2877. -/
theorem noS6A_Law2877 : ∀ v : Magma.tupS6A,
    ¬ @Equation2877 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2877) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2877) (by native_decide) v.1 v.2
    ((@Law2877.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2879 takes them (137 nodes). -/
def ordS6A_Law2879 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2879. -/
theorem noS6A_Law2879 : ∀ v : Magma.tupS6A,
    ¬ @Equation2879 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2879) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2879) (by native_decide) v.1 v.2
    ((@Law2879.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2881 takes them (56 nodes). -/
def ordS6A_Law2881 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2881. -/
theorem noS6A_Law2881 : ∀ v : Magma.tupS6A,
    ¬ @Equation2881 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2881) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2881) (by native_decide) v.1 v.2
    ((@Law2881.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2883 takes them (165 nodes). -/
def ordS6A_Law2883 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2883. -/
theorem noS6A_Law2883 : ∀ v : Magma.tupS6A,
    ¬ @Equation2883 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2883) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2883) (by native_decide) v.1 v.2
    ((@Law2883.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2884 takes them (111 nodes). -/
def ordS6A_Law2884 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2884. -/
theorem noS6A_Law2884 : ∀ v : Magma.tupS6A,
    ¬ @Equation2884 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2884) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2884) (by native_decide) v.1 v.2
    ((@Law2884.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2885 takes them (76 nodes). -/
def ordS6A_Law2885 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2885. -/
theorem noS6A_Law2885 : ∀ v : Magma.tupS6A,
    ¬ @Equation2885 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2885) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2885) (by native_decide) v.1 v.2
    ((@Law2885.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2888 takes them (160 nodes). -/
def ordS6A_Law2888 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2888. -/
theorem noS6A_Law2888 : ∀ v : Magma.tupS6A,
    ¬ @Equation2888 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2888) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2888) (by native_decide) v.1 v.2
    ((@Law2888.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2889 takes them (57 nodes). -/
def ordS6A_Law2889 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2889. -/
theorem noS6A_Law2889 : ∀ v : Magma.tupS6A,
    ¬ @Equation2889 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2889) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2889) (by native_decide) v.1 v.2
    ((@Law2889.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2891 takes them (198 nodes). -/
def ordS6A_Law2891 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2891. -/
theorem noS6A_Law2891 : ∀ v : Magma.tupS6A,
    ¬ @Equation2891 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2891) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2891) (by native_decide) v.1 v.2
    ((@Law2891.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2892 takes them (154 nodes). -/
def ordS6A_Law2892 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2892. -/
theorem noS6A_Law2892 : ∀ v : Magma.tupS6A,
    ¬ @Equation2892 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2892) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2892) (by native_decide) v.1 v.2
    ((@Law2892.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2893 takes them (61 nodes). -/
def ordS6A_Law2893 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2893. -/
theorem noS6A_Law2893 : ∀ v : Magma.tupS6A,
    ¬ @Equation2893 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2893) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2893) (by native_decide) v.1 v.2
    ((@Law2893.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2895 takes them (94 nodes). -/
def ordS6A_Law2895 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2895. -/
theorem noS6A_Law2895 : ∀ v : Magma.tupS6A,
    ¬ @Equation2895 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2895) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2895) (by native_decide) v.1 v.2
    ((@Law2895.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2896 takes them (64 nodes). -/
def ordS6A_Law2896 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2896. -/
theorem noS6A_Law2896 : ∀ v : Magma.tupS6A,
    ¬ @Equation2896 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2896) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2896) (by native_decide) v.1 v.2
    ((@Law2896.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2897 takes them (140 nodes). -/
def ordS6A_Law2897 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2897. -/
theorem noS6A_Law2897 : ∀ v : Magma.tupS6A,
    ¬ @Equation2897 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2897) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2897) (by native_decide) v.1 v.2
    ((@Law2897.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2898 takes them (29 nodes). -/
def ordS6A_Law2898 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2898. -/
theorem noS6A_Law2898 : ∀ v : Magma.tupS6A,
    ¬ @Equation2898 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2898) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2898) (by native_decide) v.1 v.2
    ((@Law2898.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2905 takes them (270 nodes). -/
def ordS6A_Law2905 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2905. -/
theorem noS6A_Law2905 : ∀ v : Magma.tupS6A,
    ¬ @Equation2905 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2905) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2905) (by native_decide) v.1 v.2
    ((@Law2905.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `22` equations. -/
theorem srch6A_refutes_27 :
    FamilyRefutes Magma.srch6A [
      2867, 2869, 2870, 2871, 2873, 2874, 2877, 2879, 2881, 2883, 2884, 2885, 2888, 2889, 2891,
      2892, 2893, 2895, 2896, 2897, 2898, 2905
    ] :=
  ⟨noS6A_Law2867, noS6A_Law2869, noS6A_Law2870, noS6A_Law2871, noS6A_Law2873, noS6A_Law2874, noS6A_Law2877, noS6A_Law2879, noS6A_Law2881, noS6A_Law2883, noS6A_Law2884, noS6A_Law2885, noS6A_Law2888, noS6A_Law2889, noS6A_Law2891, noS6A_Law2892, noS6A_Law2893, noS6A_Law2895, noS6A_Law2896, noS6A_Law2897, noS6A_Law2898, noS6A_Law2905⟩

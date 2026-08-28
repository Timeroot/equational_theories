import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 5 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 298 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2812 takes them (3 nodes). -/
def ordS8R130_Law2812 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2812. -/
theorem noS8R130_Law2812 : ∀ v : Magma.tup8R130,
    ¬ @Equation2812 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2812) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2812) (by native_decide) v.1 v.2
    ((@Law2812.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2836 takes them (3 nodes). -/
def ordS8R130_Law2836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2836. -/
theorem noS8R130_Law2836 : ∀ v : Magma.tup8R130,
    ¬ @Equation2836 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2836) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law2836) (by native_decide) v.1 v.2
    ((@Law2836.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (3 nodes). -/
def ordS8R130_Law2850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2850. -/
theorem noS8R130_Law2850 : ∀ v : Magma.tup8R130,
    ¬ @Equation2850 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2852 takes them (4 nodes). -/
def ordS8R130_Law2852 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2852. -/
theorem noS8R130_Law2852 : ∀ v : Magma.tup8R130,
    ¬ @Equation2852 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2852) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2852) (by native_decide) v.1 v.2
    ((@Law2852.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2855 takes them (4 nodes). -/
def ordS8R130_Law2855 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2855. -/
theorem noS8R130_Law2855 : ∀ v : Magma.tup8R130,
    ¬ @Equation2855 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2862 takes them (4 nodes). -/
def ordS8R130_Law2862 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2862. -/
theorem noS8R130_Law2862 : ∀ v : Magma.tup8R130,
    ¬ @Equation2862 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2862) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2862) (by native_decide) v.1 v.2
    ((@Law2862.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2863 takes them (3 nodes). -/
def ordS8R130_Law2863 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2863. -/
theorem noS8R130_Law2863 : ∀ v : Magma.tup8R130,
    ¬ @Equation2863 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2863) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2863) (by native_decide) v.1 v.2
    ((@Law2863.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2865 takes them (4 nodes). -/
def ordS8R130_Law2865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2865. -/
theorem noS8R130_Law2865 : ∀ v : Magma.tup8R130,
    ¬ @Equation2865 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2865) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2865) (by native_decide) v.1 v.2
    ((@Law2865.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2872 takes them (4 nodes). -/
def ordS8R130_Law2872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2872. -/
theorem noS8R130_Law2872 : ∀ v : Magma.tup8R130,
    ¬ @Equation2872 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2872) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2872) (by native_decide) v.1 v.2
    ((@Law2872.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2875 takes them (4 nodes). -/
def ordS8R130_Law2875 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2875. -/
theorem noS8R130_Law2875 : ∀ v : Magma.tup8R130,
    ¬ @Equation2875 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (3 nodes). -/
def ordS8R130_Law2876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2876. -/
theorem noS8R130_Law2876 : ∀ v : Magma.tup8R130,
    ¬ @Equation2876 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2880 takes them (3 nodes). -/
def ordS8R130_Law2880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2880. -/
theorem noS8R130_Law2880 : ∀ v : Magma.tup8R130,
    ¬ @Equation2880 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2880) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2880) (by native_decide) v.1 v.2
    ((@Law2880.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2882 takes them (4 nodes). -/
def ordS8R130_Law2882 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2882. -/
theorem noS8R130_Law2882 : ∀ v : Magma.tup8R130,
    ¬ @Equation2882 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2882) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2882) (by native_decide) v.1 v.2
    ((@Law2882.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2888 takes them (3 nodes). -/
def ordS8R130_Law2888 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2888. -/
theorem noS8R130_Law2888 : ∀ v : Magma.tup8R130,
    ¬ @Equation2888 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2888) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2888) (by native_decide) v.1 v.2
    ((@Law2888.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2891 takes them (3 nodes). -/
def ordS8R130_Law2891 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2891. -/
theorem noS8R130_Law2891 : ∀ v : Magma.tup8R130,
    ¬ @Equation2891 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2891) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2891) (by native_decide) v.1 v.2
    ((@Law2891.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2899 takes them (3 nodes). -/
def ordS8R130_Law2899 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2899. -/
theorem noS8R130_Law2899 : ∀ v : Magma.tup8R130,
    ¬ @Equation2899 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2899) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2899) (by native_decide) v.1 v.2
    ((@Law2899.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2902 takes them (3 nodes). -/
def ordS8R130_Law2902 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2902. -/
theorem noS8R130_Law2902 : ∀ v : Magma.tup8R130,
    ¬ @Equation2902 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2902) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2902) (by native_decide) v.1 v.2
    ((@Law2902.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (3 nodes). -/
def ordS8R130_Law2909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2909. -/
theorem noS8R130_Law2909 : ∀ v : Magma.tup8R130,
    ¬ @Equation2909 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2919 takes them (3 nodes). -/
def ordS8R130_Law2919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2919. -/
theorem noS8R130_Law2919 : ∀ v : Magma.tup8R130,
    ¬ @Equation2919 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2919) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2919) (by native_decide) v.1 v.2
    ((@Law2919.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (3 nodes). -/
def ordS8R130_Law2936 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2936. -/
theorem noS8R130_Law2936 : ∀ v : Magma.tup8R130,
    ¬ @Equation2936 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2946 takes them (3 nodes). -/
def ordS8R130_Law2946 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2946. -/
theorem noS8R130_Law2946 : ∀ v : Magma.tup8R130,
    ¬ @Equation2946 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2946) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2946) (by native_decide) v.1 v.2
    ((@Law2946.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2949 takes them (3 nodes). -/
def ordS8R130_Law2949 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2949. -/
theorem noS8R130_Law2949 : ∀ v : Magma.tup8R130,
    ¬ @Equation2949 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2949) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2949) (by native_decide) v.1 v.2
    ((@Law2949.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2956 takes them (3 nodes). -/
def ordS8R130_Law2956 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2956. -/
theorem noS8R130_Law2956 : ∀ v : Magma.tup8R130,
    ¬ @Equation2956 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2956) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2956) (by native_decide) v.1 v.2
    ((@Law2956.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2964 takes them (3 nodes). -/
def ordS8R130_Law2964 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2964. -/
theorem noS8R130_Law2964 : ∀ v : Magma.tup8R130,
    ¬ @Equation2964 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2964) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2964) (by native_decide) v.1 v.2
    ((@Law2964.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2973 takes them (3 nodes). -/
def ordS8R130_Law2973 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2973. -/
theorem noS8R130_Law2973 : ∀ v : Magma.tup8R130,
    ¬ @Equation2973 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2973) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2973) (by native_decide) v.1 v.2
    ((@Law2973.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2990 takes them (3 nodes). -/
def ordS8R130_Law2990 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2990. -/
theorem noS8R130_Law2990 : ∀ v : Magma.tup8R130,
    ¬ @Equation2990 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2990) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2990) (by native_decide) v.1 v.2
    ((@Law2990.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2998 takes them (3 nodes). -/
def ordS8R130_Law2998 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2998. -/
theorem noS8R130_Law2998 : ∀ v : Magma.tup8R130,
    ¬ @Equation2998 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2998) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2998) (by native_decide) v.1 v.2
    ((@Law2998.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3007 takes them (3 nodes). -/
def ordS8R130_Law3007 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3007. -/
theorem noS8R130_Law3007 : ∀ v : Magma.tup8R130,
    ¬ @Equation3007 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3007) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3007) (by native_decide) v.1 v.2
    ((@Law3007.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3011 takes them (3 nodes). -/
def ordS8R130_Law3011 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3011. -/
theorem noS8R130_Law3011 : ∀ v : Magma.tup8R130,
    ¬ @Equation3011 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3011) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3011) (by native_decide) v.1 v.2
    ((@Law3011.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3024 takes them (3 nodes). -/
def ordS8R130_Law3024 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3024. -/
theorem noS8R130_Law3024 : ∀ v : Magma.tup8R130,
    ¬ @Equation3024 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3024) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law3024) (by native_decide) v.1 v.2
    ((@Law3024.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (3 nodes). -/
def ordS8R130_Law3053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3053. -/
theorem noS8R130_Law3053 : ∀ v : Magma.tup8R130,
    ¬ @Equation3053 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3055 takes them (4 nodes). -/
def ordS8R130_Law3055 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3055. -/
theorem noS8R130_Law3055 : ∀ v : Magma.tup8R130,
    ¬ @Equation3055 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3055) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3055) (by native_decide) v.1 v.2
    ((@Law3055.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (3 nodes). -/
def ordS8R130_Law3056 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3056. -/
theorem noS8R130_Law3056 : ∀ v : Magma.tup8R130,
    ¬ @Equation3056 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3058 takes them (4 nodes). -/
def ordS8R130_Law3058 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3058. -/
theorem noS8R130_Law3058 : ∀ v : Magma.tup8R130,
    ¬ @Equation3058 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3058) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3058) (by native_decide) v.1 v.2
    ((@Law3058.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3059 takes them (3 nodes). -/
def ordS8R130_Law3059 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3059. -/
theorem noS8R130_Law3059 : ∀ v : Magma.tup8R130,
    ¬ @Equation3059 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3059) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3059) (by native_decide) v.1 v.2
    ((@Law3059.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3065 takes them (4 nodes). -/
def ordS8R130_Law3065 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3065. -/
theorem noS8R130_Law3065 : ∀ v : Magma.tup8R130,
    ¬ @Equation3065 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3065) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3065) (by native_decide) v.1 v.2
    ((@Law3065.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (3 nodes). -/
def ordS8R130_Law3066 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R130_Law3066 : ∀ v : Magma.tup8R130,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (4 nodes). -/
def ordS8R130_Law3068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3068. -/
theorem noS8R130_Law3068 : ∀ v : Magma.tup8R130,
    ¬ @Equation3068 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (4 nodes). -/
def ordS8R130_Law3075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3075. -/
theorem noS8R130_Law3075 : ∀ v : Magma.tup8R130,
    ¬ @Equation3075 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (4 nodes). -/
def ordS8R130_Law3078 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3078. -/
theorem noS8R130_Law3078 : ∀ v : Magma.tup8R130,
    ¬ @Equation3078 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (3 nodes). -/
def ordS8R130_Law3079 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3079. -/
theorem noS8R130_Law3079 : ∀ v : Magma.tup8R130,
    ¬ @Equation3079 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (3 nodes). -/
def ordS8R130_Law3083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R130_Law3083 : ∀ v : Magma.tup8R130,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3085 takes them (4 nodes). -/
def ordS8R130_Law3085 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3085. -/
theorem noS8R130_Law3085 : ∀ v : Magma.tup8R130,
    ¬ @Equation3085 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3085) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3085) (by native_decide) v.1 v.2
    ((@Law3085.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (3 nodes). -/
def ordS8R130_Law3091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3091. -/
theorem noS8R130_Law3091 : ∀ v : Magma.tup8R130,
    ¬ @Equation3091 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (3 nodes). -/
def ordS8R130_Law3094 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R130_Law3094 : ∀ v : Magma.tup8R130,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3102 takes them (3 nodes). -/
def ordS8R130_Law3102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3102. -/
theorem noS8R130_Law3102 : ∀ v : Magma.tup8R130,
    ¬ @Equation3102 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3102) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3102) (by native_decide) v.1 v.2
    ((@Law3102.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (3 nodes). -/
def ordS8R130_Law3112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3112. -/
theorem noS8R130_Law3112 : ∀ v : Magma.tup8R130,
    ¬ @Equation3112 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3122 takes them (3 nodes). -/
def ordS8R130_Law3122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3122. -/
theorem noS8R130_Law3122 : ∀ v : Magma.tup8R130,
    ¬ @Equation3122 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3122) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3122) (by native_decide) v.1 v.2
    ((@Law3122.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3139 takes them (3 nodes). -/
def ordS8R130_Law3139 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3139. -/
theorem noS8R130_Law3139 : ∀ v : Magma.tup8R130,
    ¬ @Equation3139 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3139) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3139) (by native_decide) v.1 v.2
    ((@Law3139.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (3 nodes). -/
def ordS8R130_Law3142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3142. -/
theorem noS8R130_Law3142 : ∀ v : Magma.tup8R130,
    ¬ @Equation3142 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3149 takes them (3 nodes). -/
def ordS8R130_Law3149 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3149. -/
theorem noS8R130_Law3149 : ∀ v : Magma.tup8R130,
    ¬ @Equation3149 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3149) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3149) (by native_decide) v.1 v.2
    ((@Law3149.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3152 takes them (3 nodes). -/
def ordS8R130_Law3152 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3152. -/
theorem noS8R130_Law3152 : ∀ v : Magma.tup8R130,
    ¬ @Equation3152 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3152) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3152) (by native_decide) v.1 v.2
    ((@Law3152.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3159 takes them (3 nodes). -/
def ordS8R130_Law3159 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3159. -/
theorem noS8R130_Law3159 : ∀ v : Magma.tup8R130,
    ¬ @Equation3159 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3159) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3159) (by native_decide) v.1 v.2
    ((@Law3159.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3167 takes them (3 nodes). -/
def ordS8R130_Law3167 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3167. -/
theorem noS8R130_Law3167 : ∀ v : Magma.tup8R130,
    ¬ @Equation3167 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3167) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3167) (by native_decide) v.1 v.2
    ((@Law3167.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3176 takes them (3 nodes). -/
def ordS8R130_Law3176 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3176. -/
theorem noS8R130_Law3176 : ∀ v : Magma.tup8R130,
    ¬ @Equation3176 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3176) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3176) (by native_decide) v.1 v.2
    ((@Law3176.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3193 takes them (3 nodes). -/
def ordS8R130_Law3193 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3193. -/
theorem noS8R130_Law3193 : ∀ v : Magma.tup8R130,
    ¬ @Equation3193 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3193) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3193) (by native_decide) v.1 v.2
    ((@Law3193.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3201 takes them (3 nodes). -/
def ordS8R130_Law3201 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3201. -/
theorem noS8R130_Law3201 : ∀ v : Magma.tup8R130,
    ¬ @Equation3201 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3201) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3201) (by native_decide) v.1 v.2
    ((@Law3201.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3210 takes them (3 nodes). -/
def ordS8R130_Law3210 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3210. -/
theorem noS8R130_Law3210 : ∀ v : Magma.tup8R130,
    ¬ @Equation3210 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3210) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3210) (by native_decide) v.1 v.2
    ((@Law3210.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3214 takes them (3 nodes). -/
def ordS8R130_Law3214 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3214. -/
theorem noS8R130_Law3214 : ∀ v : Magma.tup8R130,
    ¬ @Equation3214 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3214) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3214) (by native_decide) v.1 v.2
    ((@Law3214.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3227 takes them (3 nodes). -/
def ordS8R130_Law3227 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3227. -/
theorem noS8R130_Law3227 : ∀ v : Magma.tup8R130,
    ¬ @Equation3227 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3227) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law3227) (by native_decide) v.1 v.2
    ((@Law3227.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3254 takes them (3 nodes). -/
def ordS8R130_Law3254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3254. -/
theorem noS8R130_Law3254 : ∀ v : Magma.tup8R130,
    ¬ @Equation3254 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3254) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3254) (by native_decide) v.1 v.2
    ((@Law3254.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3255 takes them (4 nodes). -/
def ordS8R130_Law3255 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3255. -/
theorem noS8R130_Law3255 : ∀ v : Magma.tup8R130,
    ¬ @Equation3255 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3255) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3255) (by native_decide) v.1 v.2
    ((@Law3255.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3256 takes them (3 nodes). -/
def ordS8R130_Law3256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3256. -/
theorem noS8R130_Law3256 : ∀ v : Magma.tup8R130,
    ¬ @Equation3256 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3256) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3256) (by native_decide) v.1 v.2
    ((@Law3256.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3257 takes them (3 nodes). -/
def ordS8R130_Law3257 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3257. -/
theorem noS8R130_Law3257 : ∀ v : Magma.tup8R130,
    ¬ @Equation3257 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3257) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3257) (by native_decide) v.1 v.2
    ((@Law3257.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3258 takes them (4 nodes). -/
def ordS8R130_Law3258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3258. -/
theorem noS8R130_Law3258 : ∀ v : Magma.tup8R130,
    ¬ @Equation3258 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3258) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3258) (by native_decide) v.1 v.2
    ((@Law3258.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (3 nodes). -/
def ordS8R130_Law3259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3259. -/
theorem noS8R130_Law3259 : ∀ v : Magma.tup8R130,
    ¬ @Equation3259 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3261 takes them (4 nodes). -/
def ordS8R130_Law3261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3261. -/
theorem noS8R130_Law3261 : ∀ v : Magma.tup8R130,
    ¬ @Equation3261 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3261) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3261) (by native_decide) v.1 v.2
    ((@Law3261.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3262 takes them (3 nodes). -/
def ordS8R130_Law3262 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3262. -/
theorem noS8R130_Law3262 : ∀ v : Magma.tup8R130,
    ¬ @Equation3262 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3262) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3262) (by native_decide) v.1 v.2
    ((@Law3262.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3266 takes them (3 nodes). -/
def ordS8R130_Law3266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3266. -/
theorem noS8R130_Law3266 : ∀ v : Magma.tup8R130,
    ¬ @Equation3266 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3266) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3266) (by native_decide) v.1 v.2
    ((@Law3266.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3268 takes them (3 nodes). -/
def ordS8R130_Law3268 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3268. -/
theorem noS8R130_Law3268 : ∀ v : Magma.tup8R130,
    ¬ @Equation3268 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3268) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3268) (by native_decide) v.1 v.2
    ((@Law3268.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3271 takes them (3 nodes). -/
def ordS8R130_Law3271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3271. -/
theorem noS8R130_Law3271 : ∀ v : Magma.tup8R130,
    ¬ @Equation3271 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3271) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3271) (by native_decide) v.1 v.2
    ((@Law3271.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (3 nodes). -/
def ordS8R130_Law3278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3278. -/
theorem noS8R130_Law3278 : ∀ v : Magma.tup8R130,
    ¬ @Equation3278 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3281 takes them (3 nodes). -/
def ordS8R130_Law3281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3281. -/
theorem noS8R130_Law3281 : ∀ v : Magma.tup8R130,
    ¬ @Equation3281 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3288 takes them (3 nodes). -/
def ordS8R130_Law3288 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3288. -/
theorem noS8R130_Law3288 : ∀ v : Magma.tup8R130,
    ¬ @Equation3288 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3288) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3288) (by native_decide) v.1 v.2
    ((@Law3288.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3306 takes them (4 nodes). -/
def ordS8R130_Law3306 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3306. -/
theorem noS8R130_Law3306 : ∀ v : Magma.tup8R130,
    ¬ @Equation3306 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3306) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3306) (by native_decide) v.1 v.2
    ((@Law3306.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (3 nodes). -/
def ordS8R130_Law3308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3308. -/
theorem noS8R130_Law3308 : ∀ v : Magma.tup8R130,
    ¬ @Equation3308 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3309 takes them (4 nodes). -/
def ordS8R130_Law3309 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3309. -/
theorem noS8R130_Law3309 : ∀ v : Magma.tup8R130,
    ¬ @Equation3309 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3309) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3309) (by native_decide) v.1 v.2
    ((@Law3309.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3315 takes them (3 nodes). -/
def ordS8R130_Law3315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3315. -/
theorem noS8R130_Law3315 : ∀ v : Magma.tup8R130,
    ¬ @Equation3315 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3315) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3315) (by native_decide) v.1 v.2
    ((@Law3315.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3316 takes them (4 nodes). -/
def ordS8R130_Law3316 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3316. -/
theorem noS8R130_Law3316 : ∀ v : Magma.tup8R130,
    ¬ @Equation3316 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3316) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3316) (by native_decide) v.1 v.2
    ((@Law3316.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3318 takes them (3 nodes). -/
def ordS8R130_Law3318 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3318. -/
theorem noS8R130_Law3318 : ∀ v : Magma.tup8R130,
    ¬ @Equation3318 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3318) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3318) (by native_decide) v.1 v.2
    ((@Law3318.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3320 takes them (3 nodes). -/
def ordS8R130_Law3320 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3320. -/
theorem noS8R130_Law3320 : ∀ v : Magma.tup8R130,
    ¬ @Equation3320 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3320) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3320) (by native_decide) v.1 v.2
    ((@Law3320.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3323 takes them (3 nodes). -/
def ordS8R130_Law3323 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3323. -/
theorem noS8R130_Law3323 : ∀ v : Magma.tup8R130,
    ¬ @Equation3323 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3323) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3323) (by native_decide) v.1 v.2
    ((@Law3323.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (3 nodes). -/
def ordS8R130_Law3331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3331. -/
theorem noS8R130_Law3331 : ∀ v : Magma.tup8R130,
    ¬ @Equation3331 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (4 nodes). -/
def ordS8R130_Law3334 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3334. -/
theorem noS8R130_Law3334 : ∀ v : Magma.tup8R130,
    ¬ @Equation3334 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (3 nodes). -/
def ordS8R130_Law3343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3343. -/
theorem noS8R130_Law3343 : ∀ v : Magma.tup8R130,
    ¬ @Equation3343 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3346 takes them (3 nodes). -/
def ordS8R130_Law3346 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3346. -/
theorem noS8R130_Law3346 : ∀ v : Magma.tup8R130,
    ¬ @Equation3346 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3346) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3346) (by native_decide) v.1 v.2
    ((@Law3346.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3353 takes them (3 nodes). -/
def ordS8R130_Law3353 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3353. -/
theorem noS8R130_Law3353 : ∀ v : Magma.tup8R130,
    ¬ @Equation3353 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3388 takes them (3 nodes). -/
def ordS8R130_Law3388 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3388. -/
theorem noS8R130_Law3388 : ∀ v : Magma.tup8R130,
    ¬ @Equation3388 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3388) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3388) (by native_decide) v.1 v.2
    ((@Law3388.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (3 nodes). -/
def ordS8R130_Law3414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3414. -/
theorem noS8R130_Law3414 : ∀ v : Magma.tup8R130,
    ¬ @Equation3414 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3457 takes them (3 nodes). -/
def ordS8R130_Law3457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3457. -/
theorem noS8R130_Law3457 : ∀ v : Magma.tup8R130,
    ¬ @Equation3457 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3457) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3457) (by native_decide) v.1 v.2
    ((@Law3457.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (4 nodes). -/
def ordS8R130_Law3458 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3458. -/
theorem noS8R130_Law3458 : ∀ v : Magma.tup8R130,
    ¬ @Equation3458 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (3 nodes). -/
def ordS8R130_Law3459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3459. -/
theorem noS8R130_Law3459 : ∀ v : Magma.tup8R130,
    ¬ @Equation3459 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_4 :
    FamilyRefutes Magma.srch8R130 [
      2812, 2836, 2850, 2852, 2855, 2862, 2863, 2865, 2872, 2875, 2876, 2880, 2882, 2888, 2891,
      2899, 2902, 2909, 2919, 2936, 2946, 2949, 2956, 2964, 2973, 2990, 2998, 3007, 3011, 3024,
      3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3075, 3078, 3079, 3083, 3085, 3091, 3094,
      3102, 3112, 3122, 3139, 3142, 3149, 3152, 3159, 3167, 3176, 3193, 3201, 3210, 3214, 3227,
      3254, 3255, 3256, 3257, 3258, 3259, 3261, 3262, 3266, 3268, 3271, 3278, 3281, 3288, 3306,
      3308, 3309, 3315, 3316, 3318, 3320, 3323, 3331, 3334, 3343, 3346, 3353, 3388, 3414, 3457,
      3458, 3459
    ] :=
  ⟨noS8R130_Law2812, noS8R130_Law2836, noS8R130_Law2850, noS8R130_Law2852, noS8R130_Law2855, noS8R130_Law2862, noS8R130_Law2863, noS8R130_Law2865, noS8R130_Law2872, noS8R130_Law2875, noS8R130_Law2876, noS8R130_Law2880, noS8R130_Law2882, noS8R130_Law2888, noS8R130_Law2891, noS8R130_Law2899, noS8R130_Law2902, noS8R130_Law2909, noS8R130_Law2919, noS8R130_Law2936, noS8R130_Law2946, noS8R130_Law2949, noS8R130_Law2956, noS8R130_Law2964, noS8R130_Law2973, noS8R130_Law2990, noS8R130_Law2998, noS8R130_Law3007, noS8R130_Law3011, noS8R130_Law3024, noS8R130_Law3053, noS8R130_Law3055, noS8R130_Law3056, noS8R130_Law3058, noS8R130_Law3059, noS8R130_Law3065, noS8R130_Law3066, noS8R130_Law3068, noS8R130_Law3075, noS8R130_Law3078, noS8R130_Law3079, noS8R130_Law3083, noS8R130_Law3085, noS8R130_Law3091, noS8R130_Law3094, noS8R130_Law3102, noS8R130_Law3112, noS8R130_Law3122, noS8R130_Law3139, noS8R130_Law3142, noS8R130_Law3149, noS8R130_Law3152, noS8R130_Law3159, noS8R130_Law3167, noS8R130_Law3176, noS8R130_Law3193, noS8R130_Law3201, noS8R130_Law3210, noS8R130_Law3214, noS8R130_Law3227, noS8R130_Law3254, noS8R130_Law3255, noS8R130_Law3256, noS8R130_Law3257, noS8R130_Law3258, noS8R130_Law3259, noS8R130_Law3261, noS8R130_Law3262, noS8R130_Law3266, noS8R130_Law3268, noS8R130_Law3271, noS8R130_Law3278, noS8R130_Law3281, noS8R130_Law3288, noS8R130_Law3306, noS8R130_Law3308, noS8R130_Law3309, noS8R130_Law3315, noS8R130_Law3316, noS8R130_Law3318, noS8R130_Law3320, noS8R130_Law3323, noS8R130_Law3331, noS8R130_Law3334, noS8R130_Law3343, noS8R130_Law3346, noS8R130_Law3353, noS8R130_Law3388, noS8R130_Law3414, noS8R130_Law3457, noS8R130_Law3458, noS8R130_Law3459⟩

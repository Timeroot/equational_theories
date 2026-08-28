import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 12 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 3,512 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2855 takes them (825 nodes). -/
def ordS8R52_Law2855 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2855. -/
theorem noS8R52_Law2855 : ∀ v : Magma.tup8R52,
    ¬ @Equation2855 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2858 takes them (299 nodes). -/
def ordS8R52_Law2858 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2858. -/
theorem noS8R52_Law2858 : ∀ v : Magma.tup8R52,
    ¬ @Equation2858 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2858) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2858) (by native_decide) v.1 v.2
    ((@Law2858.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2868 takes them (387 nodes). -/
def ordS8R52_Law2868 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2868. -/
theorem noS8R52_Law2868 : ∀ v : Magma.tup8R52,
    ¬ @Equation2868 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2868) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2868) (by native_decide) v.1 v.2
    ((@Law2868.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2878 takes them (265 nodes). -/
def ordS8R52_Law2878 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2878. -/
theorem noS8R52_Law2878 : ∀ v : Magma.tup8R52,
    ¬ @Equation2878 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2878) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2878) (by native_decide) v.1 v.2
    ((@Law2878.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2890 takes them (362 nodes). -/
def ordS8R52_Law2890 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2890. -/
theorem noS8R52_Law2890 : ∀ v : Magma.tup8R52,
    ¬ @Equation2890 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2890) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2890) (by native_decide) v.1 v.2
    ((@Law2890.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2894 takes them (262 nodes). -/
def ordS8R52_Law2894 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2894. -/
theorem noS8R52_Law2894 : ∀ v : Magma.tup8R52,
    ¬ @Equation2894 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2894) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2894) (by native_decide) v.1 v.2
    ((@Law2894.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (296 nodes). -/
def ordS8R52_Law2909 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2909. -/
theorem noS8R52_Law2909 : ∀ v : Magma.tup8R52,
    ¬ @Equation2909 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2919 takes them (166 nodes). -/
def ordS8R52_Law2919 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2919. -/
theorem noS8R52_Law2919 : ∀ v : Magma.tup8R52,
    ¬ @Equation2919 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2919) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2919) (by native_decide) v.1 v.2
    ((@Law2919.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2946 takes them (318 nodes). -/
def ordS8R52_Law2946 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2946. -/
theorem noS8R52_Law2946 : ∀ v : Magma.tup8R52,
    ¬ @Equation2946 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2946) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2946) (by native_decide) v.1 v.2
    ((@Law2946.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2956 takes them (158 nodes). -/
def ordS8R52_Law2956 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2956. -/
theorem noS8R52_Law2956 : ∀ v : Magma.tup8R52,
    ¬ @Equation2956 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2956) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2956) (by native_decide) v.1 v.2
    ((@Law2956.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2990 takes them (174 nodes). -/
def ordS8R52_Law2990 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2990. -/
theorem noS8R52_Law2990 : ∀ v : Magma.tup8R52,
    ¬ @Equation2990 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2990) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2990) (by native_decide) v.1 v.2
    ((@Law2990.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch8R52_refutes_11 :
    FamilyRefutes Magma.srch8R52 [
      2855, 2858, 2868, 2878, 2890, 2894, 2909, 2919, 2946, 2956, 2990
    ] :=
  ⟨noS8R52_Law2855, noS8R52_Law2858, noS8R52_Law2868, noS8R52_Law2878, noS8R52_Law2890, noS8R52_Law2894, noS8R52_Law2909, noS8R52_Law2919, noS8R52_Law2946, noS8R52_Law2956, noS8R52_Law2990⟩

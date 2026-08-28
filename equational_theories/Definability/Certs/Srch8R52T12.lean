import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 13 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,317 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3007 takes them (166 nodes). -/
def ordS8R52_Law3007 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3007. -/
theorem noS8R52_Law3007 : ∀ v : Magma.tup8R52,
    ¬ @Equation3007 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3007) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3007) (by native_decide) v.1 v.2
    ((@Law3007.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3024 takes them (158 nodes). -/
def ordS8R52_Law3024 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3024. -/
theorem noS8R52_Law3024 : ∀ v : Magma.tup8R52,
    ¬ @Equation3024 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3024) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law3024) (by native_decide) v.1 v.2
    ((@Law3024.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (945 nodes). -/
def ordS8R52_Law3053 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3053. -/
theorem noS8R52_Law3053 : ∀ v : Magma.tup8R52,
    ¬ @Equation3053 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3061 takes them (368 nodes). -/
def ordS8R52_Law3061 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3061. -/
theorem noS8R52_Law3061 : ∀ v : Magma.tup8R52,
    ¬ @Equation3061 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3061) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3061) (by native_decide) v.1 v.2
    ((@Law3061.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (545 nodes). -/
def ordS8R52_Law3066 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R52_Law3066 : ∀ v : Magma.tup8R52,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3081 takes them (329 nodes). -/
def ordS8R52_Law3081 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3081. -/
theorem noS8R52_Law3081 : ∀ v : Magma.tup8R52,
    ¬ @Equation3081 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3081) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3081) (by native_decide) v.1 v.2
    ((@Law3081.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (481 nodes). -/
def ordS8R52_Law3083 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R52_Law3083 : ∀ v : Magma.tup8R52,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3089 takes them (325 nodes). -/
def ordS8R52_Law3089 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3089. -/
theorem noS8R52_Law3089 : ∀ v : Magma.tup8R52,
    ¬ @Equation3089 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3089) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3089) (by native_decide) v.1 v.2
    ((@Law3089.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R52_refutes_12 :
    FamilyRefutes Magma.srch8R52 [
      3007, 3024, 3053, 3061, 3066, 3081, 3083, 3089
    ] :=
  ⟨noS8R52_Law3007, noS8R52_Law3024, noS8R52_Law3053, noS8R52_Law3061, noS8R52_Law3066, noS8R52_Law3081, noS8R52_Law3083, noS8R52_Law3089⟩

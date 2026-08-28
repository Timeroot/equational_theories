import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 14 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,422 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3093 takes them (328 nodes). -/
def ordS8R52_Law3093 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3093. -/
theorem noS8R52_Law3093 : ∀ v : Magma.tup8R52,
    ¬ @Equation3093 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3093) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3093) (by native_decide) v.1 v.2
    ((@Law3093.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (417 nodes). -/
def ordS8R52_Law3094 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R52_Law3094 : ∀ v : Magma.tup8R52,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3097 takes them (325 nodes). -/
def ordS8R52_Law3097 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3097. -/
theorem noS8R52_Law3097 : ∀ v : Magma.tup8R52,
    ¬ @Equation3097 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3097) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law3097) (by native_decide) v.1 v.2
    ((@Law3097.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (288 nodes). -/
def ordS8R52_Law3112 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3112. -/
theorem noS8R52_Law3112 : ∀ v : Magma.tup8R52,
    ¬ @Equation3112 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3122 takes them (158 nodes). -/
def ordS8R52_Law3122 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3122. -/
theorem noS8R52_Law3122 : ∀ v : Magma.tup8R52,
    ¬ @Equation3122 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3122) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3122) (by native_decide) v.1 v.2
    ((@Law3122.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3149 takes them (318 nodes). -/
def ordS8R52_Law3149 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3149. -/
theorem noS8R52_Law3149 : ∀ v : Magma.tup8R52,
    ¬ @Equation3149 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3149) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3149) (by native_decide) v.1 v.2
    ((@Law3149.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3159 takes them (158 nodes). -/
def ordS8R52_Law3159 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3159. -/
theorem noS8R52_Law3159 : ∀ v : Magma.tup8R52,
    ¬ @Equation3159 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3159) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3159) (by native_decide) v.1 v.2
    ((@Law3159.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3193 takes them (158 nodes). -/
def ordS8R52_Law3193 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3193. -/
theorem noS8R52_Law3193 : ∀ v : Magma.tup8R52,
    ¬ @Equation3193 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3193) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3193) (by native_decide) v.1 v.2
    ((@Law3193.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3210 takes them (174 nodes). -/
def ordS8R52_Law3210 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3210. -/
theorem noS8R52_Law3210 : ∀ v : Magma.tup8R52,
    ¬ @Equation3210 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3210) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3210) (by native_decide) v.1 v.2
    ((@Law3210.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3227 takes them (158 nodes). -/
def ordS8R52_Law3227 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3227. -/
theorem noS8R52_Law3227 : ∀ v : Magma.tup8R52,
    ¬ @Equation3227 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3227) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law3227) (by native_decide) v.1 v.2
    ((@Law3227.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (521 nodes). -/
def ordS8R52_Law3278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3278. -/
theorem noS8R52_Law3278 : ∀ v : Magma.tup8R52,
    ¬ @Equation3278 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (419 nodes). -/
def ordS8R52_Law3334 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3334. -/
theorem noS8R52_Law3334 : ∀ v : Magma.tup8R52,
    ¬ @Equation3334 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch8R52_refutes_13 :
    FamilyRefutes Magma.srch8R52 [
      3093, 3094, 3097, 3112, 3122, 3149, 3159, 3193, 3210, 3227, 3278, 3334
    ] :=
  ⟨noS8R52_Law3093, noS8R52_Law3094, noS8R52_Law3097, noS8R52_Law3112, noS8R52_Law3122, noS8R52_Law3149, noS8R52_Law3159, noS8R52_Law3193, noS8R52_Law3210, noS8R52_Law3227, noS8R52_Law3278, noS8R52_Law3334⟩

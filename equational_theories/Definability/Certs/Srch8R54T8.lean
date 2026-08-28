import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 9 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,398 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3083 takes them (705 nodes). -/
def ordS8R54_Law3083 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R54_Law3083 : ∀ v : Magma.tup8R54,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (705 nodes). -/
def ordS8R54_Law3094 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R54_Law3094 : ∀ v : Magma.tup8R54,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (809 nodes). -/
def ordS8R54_Law3278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3278. -/
theorem noS8R54_Law3278 : ∀ v : Magma.tup8R54,
    ¬ @Equation3278 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (165 nodes). -/
def ordS8R54_Law3308 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3308. -/
theorem noS8R54_Law3308 : ∀ v : Magma.tup8R54,
    ¬ @Equation3308 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (807 nodes). -/
def ordS8R54_Law3334 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3334. -/
theorem noS8R54_Law3334 : ∀ v : Magma.tup8R54,
    ¬ @Equation3334 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (207 nodes). -/
def ordS8R54_Law3343 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3343. -/
theorem noS8R54_Law3343 : ∀ v : Magma.tup8R54,
    ¬ @Equation3343 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R54_refutes_8 :
    FamilyRefutes Magma.srch8R54 [
      3083, 3094, 3278, 3308, 3334, 3343
    ] :=
  ⟨noS8R54_Law3083, noS8R54_Law3094, noS8R54_Law3278, noS8R54_Law3308, noS8R54_Law3334, noS8R54_Law3343⟩

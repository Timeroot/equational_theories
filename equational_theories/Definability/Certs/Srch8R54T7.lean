import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 8 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,571 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2485 takes them (713 nodes). -/
def ordS8R54_Law2485 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2485. -/
theorem noS8R54_Law2485 : ∀ v : Magma.tup8R54,
    ¬ @Equation2485 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (293 nodes). -/
def ordS8R54_Law2653 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2653. -/
theorem noS8R54_Law2653 : ∀ v : Magma.tup8R54,
    ¬ @Equation2653 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (209 nodes). -/
def ordS8R54_Law2663 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2663. -/
theorem noS8R54_Law2663 : ∀ v : Magma.tup8R54,
    ¬ @Equation2663 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (530 nodes). -/
def ordS8R54_Law2850 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2850. -/
theorem noS8R54_Law2850 : ∀ v : Magma.tup8R54,
    ¬ @Equation2850 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (1121 nodes). -/
def ordS8R54_Law3053 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3053. -/
theorem noS8R54_Law3053 : ∀ v : Magma.tup8R54,
    ¬ @Equation3053 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (705 nodes). -/
def ordS8R54_Law3066 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R54_Law3066 : ∀ v : Magma.tup8R54,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R54_refutes_7 :
    FamilyRefutes Magma.srch8R54 [
      2485, 2653, 2663, 2850, 3053, 3066
    ] :=
  ⟨noS8R54_Law2485, noS8R54_Law2653, noS8R54_Law2663, noS8R54_Law2850, noS8R54_Law3053, noS8R54_Law3066⟩

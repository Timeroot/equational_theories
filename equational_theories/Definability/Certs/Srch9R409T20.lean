import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 21 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 1,579 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3089 takes them (833 nodes). -/
def ordS9R409_Law3089 : List (Fin 12) := [8, 6, 10, 0, 7, 5, 11, 9, 3, 4, 1, 2]

/-- No member of the class satisfies equation 3089. -/
theorem noS9R409_Law3089 : ∀ v : Magma.tup9R409,
    ¬ @Equation3089 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3089) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law3089) (by native_decide) v.1 v.2
    ((@Law3089.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3097 takes them (746 nodes). -/
def ordS9R409_Law3097 : List (Fin 12) := [2, 9, 6, 11, 8, 4, 0, 10, 5, 1, 7, 3]

/-- No member of the class satisfies equation 3097. -/
theorem noS9R409_Law3097 : ∀ v : Magma.tup9R409,
    ¬ @Equation3097 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3097) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law3097) (by native_decide) v.1 v.2
    ((@Law3097.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R409_refutes_20 :
    FamilyRefutes Magma.srch9R409 [
      3089, 3097
    ] :=
  ⟨noS9R409_Law3089, noS9R409_Law3097⟩

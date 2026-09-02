import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 15 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,690 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2070 takes them (2678 nodes). -/
def ordS9R409_Law2070 : List (Fin 12) := [5, 10, 0, 6, 9, 11, 8, 7, 3, 1, 4, 2]

/-- No member of the class satisfies equation 2070. -/
theorem noS9R409_Law2070 : ∀ v : Magma.tup9R409,
    ¬ @Equation2070 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2070) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2070) (by native_decide) v.1 v.2
    ((@Law2070.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2675 takes them (1012 nodes). -/
def ordS9R409_Law2675 : List (Fin 12) := [11, 2, 9, 5, 10, 3, 4, 0, 8, 7, 6, 1]

/-- No member of the class satisfies equation 2675. -/
theorem noS9R409_Law2675 : ∀ v : Magma.tup9R409,
    ¬ @Equation2675 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2675) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2675) (by native_decide) v.1 v.2
    ((@Law2675.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R409_refutes_14 :
    FamilyRefutes Magma.srch9R409 [
      2070, 2675
    ] :=
  ⟨noS9R409_Law2070, noS9R409_Law2675⟩

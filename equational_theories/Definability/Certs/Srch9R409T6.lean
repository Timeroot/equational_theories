import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 7 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,023 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 645 takes them (621 nodes). -/
def ordS9R409_Law645 : List (Fin 12) := [11, 0, 10, 8, 7, 6, 9, 2, 4, 5, 3, 1]

/-- No member of the class satisfies equation 645. -/
theorem noS9R409_Law645 : ∀ v : Magma.tup9R409,
    ¬ @Equation645 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law645) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law645) (by native_decide) v.1 v.2
    ((@Law645.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 649 takes them (956 nodes). -/
def ordS9R409_Law649 : List (Fin 12) := [10, 5, 7, 9, 6, 4, 3, 2, 8, 11, 0, 1]

/-- No member of the class satisfies equation 649. -/
theorem noS9R409_Law649 : ∀ v : Magma.tup9R409,
    ¬ @Equation649 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law649) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law649) (by native_decide) v.1 v.2
    ((@Law649.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 653 takes them (1446 nodes). -/
def ordS9R409_Law653 : List (Fin 12) := [3, 9, 8, 10, 7, 2, 11, 4, 1, 0, 5, 6]

/-- No member of the class satisfies equation 653. -/
theorem noS9R409_Law653 : ∀ v : Magma.tup9R409,
    ¬ @Equation653 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law653) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law653) (by native_decide) v.1 v.2
    ((@Law653.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R409_refutes_6 :
    FamilyRefutes Magma.srch9R409 [
      645, 649, 653
    ] :=
  ⟨noS9R409_Law645, noS9R409_Law649, noS9R409_Law653⟩

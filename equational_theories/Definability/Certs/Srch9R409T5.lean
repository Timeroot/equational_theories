import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 6 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 3,891 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 642 takes them (3891 nodes). -/
def ordS9R409_Law642 : List (Fin 12) := [6, 10, 2, 8, 9, 11, 5, 7, 0, 4, 1, 3]

/-- No member of the class satisfies equation 642. -/
theorem noS9R409_Law642 : ∀ v : Magma.tup9R409,
    ¬ @Equation642 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law642) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 2)
    (ord := ordS9R409_Law642) (by native_decide) v.1 v.2
    ((@Law642.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R409_refutes_5 :
    FamilyRefutes Magma.srch9R409 [
      642
    ] :=
  noS9R409_Law642

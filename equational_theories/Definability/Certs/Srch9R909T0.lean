import equational_theories.Definability.Srch_S9R909

/-!
# Structural certificate targets: `Magma.srch9R909` (part 1 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R909_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 23,692 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R909_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 14 takes them (23692 nodes). -/
def ordS9R909_Law14 : List (Fin 9) := [8, 1, 4, 6, 2, 5, 7, 3, 0]

/-- No member of the class satisfies equation 14. -/
theorem noS9R909_Law14 : ∀ v : Magma.tup9R909,
    ¬ @Equation14 (Fin 9) (Magma.srch9R909 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law14) (E := S9R909.E) (tr := S9R909.tr) (z := S9R909.z)
    (st := S9R909.st) (X := S9R909.X) (envs := Magma.envsRed 9 S9R909.E 2)
    (ord := ordS9R909_Law14) (by native_decide) v.1 v.2
    ((@Law14.models_iff (Fin 9) (Magma.srch9R909 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R909_refutes_0 :
    FamilyRefutes Magma.srch9R909 [
      14
    ] :=
  noS9R909_Law14

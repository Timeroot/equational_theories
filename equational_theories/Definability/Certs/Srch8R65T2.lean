import equational_theories.Definability.Srch_S8R65

/-!
# Structural certificate targets: `Magma.srch8R65` (part 3 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R65_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 15,261 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R65_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 828 takes them (15261 nodes). -/
def ordS8R65_Law828 : List (Fin 17) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-- No member of the class satisfies equation 828. -/
theorem noS8R65_Law828 : ∀ v : Magma.tup8R65,
    ¬ @Equation828 (Fin 8) (Magma.srch8R65 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law828) (E := S8R65.E) (tr := S8R65.tr) (z := S8R65.z)
    (st := S8R65.st) (X := S8R65.X) (envs := Magma.envsRed 8 S8R65.E 3)
    (ord := ordS8R65_Law828) (by native_decide) v.1 v.2
    ((@Law828.models_iff (Fin 8) (Magma.srch8R65 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R65_refutes_2 :
    FamilyRefutes Magma.srch8R65 [
      828
    ] :=
  noS8R65_Law828

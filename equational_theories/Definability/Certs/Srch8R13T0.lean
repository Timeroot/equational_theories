import equational_theories.Definability.Srch_S8R13

/-!
# Structural certificate targets: `Magma.srch8R13` (part 1 of 85)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 940 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 62 takes them (940 nodes). -/
def ordS8R13_Law62 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 62. -/
theorem noS8R13_Law62 : ∀ v : Magma.tup8R13,
    ¬ @Equation62 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law62) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 2)
    (ord := ordS8R13_Law62) (by native_decide) v.1 v.2
    ((@Law62.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R13_refutes_0 :
    FamilyRefutes Magma.srch8R13 [
      62
    ] :=
  noS8R13_Law62

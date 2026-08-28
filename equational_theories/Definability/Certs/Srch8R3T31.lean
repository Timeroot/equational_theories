import equational_theories.Definability.Srch_S8R3

/-!
# Structural certificate targets: `Magma.srch8R3` (part 32 of 77)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 7,250 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3866 takes them (7250 nodes). -/
def ordS8R3_Law3866 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 3866. -/
theorem noS8R3_Law3866 : ∀ v : Magma.tup8R3,
    ¬ @Equation3866 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3866) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 3)
    (ord := ordS8R3_Law3866) (by native_decide) v.1 v.2
    ((@Law3866.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R3_refutes_31 :
    FamilyRefutes Magma.srch8R3 [
      3866
    ] :=
  noS8R3_Law3866

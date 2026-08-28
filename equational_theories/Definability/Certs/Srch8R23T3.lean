import equational_theories.Definability.Srch_S8R23

/-!
# Structural certificate targets: `Magma.srch8R23` (part 4 of 6)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R23_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 14,389 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R23_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3601 takes them (14389 nodes). -/
def ordS8R23_Law3601 : List (Fin 20) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

/-- No member of the class satisfies equation 3601. -/
theorem noS8R23_Law3601 : ∀ v : Magma.tup8R23,
    ¬ @Equation3601 (Fin 8) (Magma.srch8R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3601) (E := S8R23.E) (tr := S8R23.tr) (z := S8R23.z)
    (st := S8R23.st) (X := S8R23.X) (envs := Magma.envsRed 8 S8R23.E 3)
    (ord := ordS8R23_Law3601) (by native_decide) v.1 v.2
    ((@Law3601.models_iff (Fin 8) (Magma.srch8R23 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R23_refutes_3 :
    FamilyRefutes Magma.srch8R23 [
      3601
    ] :=
  noS8R23_Law3601

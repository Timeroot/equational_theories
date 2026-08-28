import equational_theories.Definability.Srch_S8R44

/-!
# Structural certificate targets: `Magma.srch8R44` (part 52 of 64)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R44_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 8,140 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R44_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3935 takes them (8140 nodes). -/
def ordS8R44_Law3935 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3935. -/
theorem noS8R44_Law3935 : ∀ v : Magma.tup8R44,
    ¬ @Equation3935 (Fin 8) (Magma.srch8R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3935) (E := S8R44.E) (tr := S8R44.tr) (z := S8R44.z)
    (st := S8R44.st) (X := S8R44.X) (envs := Magma.envsRed 8 S8R44.E 3)
    (ord := ordS8R44_Law3935) (by native_decide) v.1 v.2
    ((@Law3935.models_iff (Fin 8) (Magma.srch8R44 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R44_refutes_51 :
    FamilyRefutes Magma.srch8R44 [
      3935
    ] :=
  noS8R44_Law3935

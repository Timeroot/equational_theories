import equational_theories.Definability.Srch_S8R49

/-!
# Structural certificate targets: `Magma.srch8R49` (part 7 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R49_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,185 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R49_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4398 takes them (2185 nodes). -/
def ordS8R49_Law4398 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4398. -/
theorem noS8R49_Law4398 : ∀ v : Magma.tup8R49,
    ¬ @Equation4398 (Fin 8) (Magma.srch8R49 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S8R49.E) (tr := S8R49.tr) (z := S8R49.z)
    (st := S8R49.st) (X := S8R49.X) (envs := Magma.envsRed 8 S8R49.E 2)
    (ord := ordS8R49_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 8) (Magma.srch8R49 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R49_refutes_6 :
    FamilyRefutes Magma.srch8R49 [
      4398
    ] :=
  noS8R49_Law4398

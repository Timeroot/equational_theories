import equational_theories.Definability.Srch_S8R406

/-!
# Structural certificate targets: `Magma.srch8R406` (part 8 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R406_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 26,095 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R406_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2900 takes them (26095 nodes). -/
def ordS8R406_Law2900 : List (Fin 10) := [9, 0, 3, 2, 8, 1, 4, 6, 7, 5]

/-- No member of the class satisfies equation 2900. -/
theorem noS8R406_Law2900 : ∀ v : Magma.tup8R406,
    ¬ @Equation2900 (Fin 8) (Magma.srch8R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2900) (E := S8R406.E) (tr := S8R406.tr) (z := S8R406.z)
    (st := S8R406.st) (X := S8R406.X) (envs := Magma.envsRed 8 S8R406.E 2)
    (ord := ordS8R406_Law2900) (by native_decide) v.1 v.2
    ((@Law2900.models_iff (Fin 8) (Magma.srch8R406 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R406_refutes_7 :
    FamilyRefutes Magma.srch8R406 [
      2900
    ] :=
  noS8R406_Law2900

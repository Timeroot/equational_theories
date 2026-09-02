import equational_theories.Definability.Srch_S8R406

/-!
# Structural certificate targets: `Magma.srch8R406` (part 2 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R406_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 20,277 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R406_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 917 takes them (20277 nodes). -/
def ordS8R406_Law917 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 917. -/
theorem noS8R406_Law917 : ∀ v : Magma.tup8R406,
    ¬ @Equation917 (Fin 8) (Magma.srch8R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law917) (E := S8R406.E) (tr := S8R406.tr) (z := S8R406.z)
    (st := S8R406.st) (X := S8R406.X) (envs := Magma.envsRed 8 S8R406.E 2)
    (ord := ordS8R406_Law917) (by native_decide) v.1 v.2
    ((@Law917.models_iff (Fin 8) (Magma.srch8R406 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R406_refutes_1 :
    FamilyRefutes Magma.srch8R406 [
      917
    ] :=
  noS8R406_Law917

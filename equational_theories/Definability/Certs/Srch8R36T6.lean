import equational_theories.Definability.Srch_S8R36

/-!
# Structural certificate targets: `Magma.srch8R36` (part 7 of 12)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R36_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,375 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R36_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3321 takes them (2375 nodes). -/
def ordS8R36_Law3321 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 3321. -/
theorem noS8R36_Law3321 : ∀ v : Magma.tup8R36,
    ¬ @Equation3321 (Fin 8) (Magma.srch8R36 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S8R36.E) (tr := S8R36.tr) (z := S8R36.z)
    (st := S8R36.st) (X := S8R36.X) (envs := Magma.envsRed 8 S8R36.E 3)
    (ord := ordS8R36_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 8) (Magma.srch8R36 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R36_refutes_6 :
    FamilyRefutes Magma.srch8R36 [
      3321
    ] :=
  noS8R36_Law3321

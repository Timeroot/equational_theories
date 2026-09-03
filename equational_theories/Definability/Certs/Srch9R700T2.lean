import equational_theories.Definability.Srch_S9R700

/-!
# Structural certificate targets: `Magma.srch9R700` (part 3 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R700_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 478 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R700_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4006 takes them (478 nodes). -/
def ordS9R700_Law4006 : List (Fin 11) := [9, 6, 5, 7, 10, 0, 8, 2, 1, 4, 3]

/-- No member of the class satisfies equation 4006. -/
theorem noS9R700_Law4006 : ∀ v : Magma.tup9R700,
    ¬ @Equation4006 (Fin 9) (Magma.srch9R700 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S9R700.E) (tr := S9R700.tr) (z := S9R700.z)
    (st := S9R700.st) (X := S9R700.X) (envs := Magma.envsRed 9 S9R700.E 3)
    (ord := ordS9R700_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 9) (Magma.srch9R700 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R700_refutes_2 :
    FamilyRefutes Magma.srch9R700 [
      4006
    ] :=
  noS9R700_Law4006

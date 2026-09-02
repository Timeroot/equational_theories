import equational_theories.Definability.Srch_S9R404

/-!
# Structural certificate targets: `Magma.srch9R404` (part 4 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R404_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 21,356 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R404_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4131 takes them (21356 nodes). -/
def ordS9R404_Law4131 : List (Fin 9) := [4, 5, 7, 3, 1, 0, 8, 2, 6]

/-- No member of the class satisfies equation 4131. -/
theorem noS9R404_Law4131 : ∀ v : Magma.tup9R404,
    ¬ @Equation4131 (Fin 9) (Magma.srch9R404 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4131) (E := S9R404.E) (tr := S9R404.tr) (z := S9R404.z)
    (st := S9R404.st) (X := S9R404.X) (envs := Magma.envsRed 9 S9R404.E 2)
    (ord := ordS9R404_Law4131) (by native_decide) v.1 v.2
    ((@Law4131.models_iff (Fin 9) (Magma.srch9R404 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R404_refutes_3 :
    FamilyRefutes Magma.srch9R404 [
      4131
    ] :=
  noS9R404_Law4131

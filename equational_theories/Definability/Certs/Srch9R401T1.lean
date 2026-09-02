import equational_theories.Definability.Srch_S9R401

/-!
# Structural certificate targets: `Magma.srch9R401` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R401_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 1,897 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R401_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3079 takes them (1897 nodes). -/
def ordS9R401_Law3079 : List (Fin 9) := [6, 0, 3, 8, 2, 5, 7, 4, 1]

/-- No member of the class satisfies equation 3079. -/
theorem noS9R401_Law3079 : ∀ v : Magma.tup9R401,
    ¬ @Equation3079 (Fin 9) (Magma.srch9R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S9R401.E) (tr := S9R401.tr) (z := S9R401.z)
    (st := S9R401.st) (X := S9R401.X) (envs := Magma.envsRed 9 S9R401.E 2)
    (ord := ordS9R401_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 9) (Magma.srch9R401 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R401_refutes_1 :
    FamilyRefutes Magma.srch9R401 [
      3079
    ] :=
  noS9R401_Law3079

import equational_theories.Definability.Srch_S9R910

/-!
# Structural certificate targets: `Magma.srch9R910` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R910_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 149,540 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R910_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 125 takes them (149540 nodes). -/
def ordS9R910_Law125 : List (Fin 11) := [2, 9, 1, 10, 0, 6, 7, 4, 8, 5, 3]

/-- No member of the class satisfies equation 125. -/
theorem noS9R910_Law125 : ∀ v : Magma.tup9R910,
    ¬ @Equation125 (Fin 9) (Magma.srch9R910 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law125) (E := S9R910.E) (tr := S9R910.tr) (z := S9R910.z)
    (st := S9R910.st) (X := S9R910.X) (envs := Magma.envsRed 9 S9R910.E 2)
    (ord := ordS9R910_Law125) (by native_decide) v.1 v.2
    ((@Law125.models_iff (Fin 9) (Magma.srch9R910 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R910_refutes_3 :
    FamilyRefutes Magma.srch9R910 [
      125
    ] :=
  noS9R910_Law125

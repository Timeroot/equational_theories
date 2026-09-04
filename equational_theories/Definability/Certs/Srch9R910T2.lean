import equational_theories.Definability.Srch_S9R910

/-!
# Structural certificate targets: `Magma.srch9R910` (part 3 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R910_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 148,821 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R910_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 118 takes them (148821 nodes). -/
def ordS9R910_Law118 : List (Fin 11) := [4, 2, 10, 1, 8, 0, 7, 9, 3, 6, 5]

/-- No member of the class satisfies equation 118. -/
theorem noS9R910_Law118 : ∀ v : Magma.tup9R910,
    ¬ @Equation118 (Fin 9) (Magma.srch9R910 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law118) (E := S9R910.E) (tr := S9R910.tr) (z := S9R910.z)
    (st := S9R910.st) (X := S9R910.X) (envs := Magma.envsRed 9 S9R910.E 2)
    (ord := ordS9R910_Law118) (by native_decide) v.1 v.2
    ((@Law118.models_iff (Fin 9) (Magma.srch9R910 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R910_refutes_2 :
    FamilyRefutes Magma.srch9R910 [
      118
    ] :=
  noS9R910_Law118

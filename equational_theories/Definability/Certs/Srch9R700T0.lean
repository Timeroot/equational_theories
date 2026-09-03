import equational_theories.Definability.Srch_S9R700

/-!
# Structural certificate targets: `Magma.srch9R700` (part 1 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R700_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 6,563 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R700_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1654 takes them (6563 nodes). -/
def ordS9R700_Law1654 : List (Fin 11) := [5, 10, 8, 0, 9, 4, 2, 3, 6, 1, 7]

/-- No member of the class satisfies equation 1654. -/
theorem noS9R700_Law1654 : ∀ v : Magma.tup9R700,
    ¬ @Equation1654 (Fin 9) (Magma.srch9R700 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S9R700.E) (tr := S9R700.tr) (z := S9R700.z)
    (st := S9R700.st) (X := S9R700.X) (envs := Magma.envsRed 9 S9R700.E 2)
    (ord := ordS9R700_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 9) (Magma.srch9R700 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R700_refutes_0 :
    FamilyRefutes Magma.srch9R700 [
      1654
    ] :=
  noS9R700_Law1654

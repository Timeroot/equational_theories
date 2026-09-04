import equational_theories.Definability.Srch_S9R910

/-!
# Structural certificate targets: `Magma.srch9R910` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R910_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 283,512 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R910_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1692 takes them (283512 nodes). -/
def ordS9R910_Law1692 : List (Fin 11) := [0, 2, 10, 3, 8, 6, 5, 4, 7, 9, 1]

/-- No member of the class satisfies equation 1692. -/
theorem noS9R910_Law1692 : ∀ v : Magma.tup9R910,
    ¬ @Equation1692 (Fin 9) (Magma.srch9R910 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1692) (E := S9R910.E) (tr := S9R910.tr) (z := S9R910.z)
    (st := S9R910.st) (X := S9R910.X) (envs := Magma.envsRed 9 S9R910.E 2)
    (ord := ordS9R910_Law1692) (by native_decide) v.1 v.2
    ((@Law1692.models_iff (Fin 9) (Magma.srch9R910 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R910_refutes_4 :
    FamilyRefutes Magma.srch9R910 [
      1692
    ] :=
  noS9R910_Law1692

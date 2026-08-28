import equational_theories.Definability.Srch_S8R26

/-!
# Structural certificate targets: `Magma.srch8R26` (part 7 of 12)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R26_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 4,610 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R26_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 864 takes them (4610 nodes). -/
def ordS8R26_Law864 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 864. -/
theorem noS8R26_Law864 : ∀ v : Magma.tup8R26,
    ¬ @Equation864 (Fin 8) (Magma.srch8R26 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law864) (E := S8R26.E) (tr := S8R26.tr) (z := S8R26.z)
    (st := S8R26.st) (X := S8R26.X) (envs := Magma.envsRed 8 S8R26.E 4)
    (ord := ordS8R26_Law864) (by native_decide) v.1 v.2
    ((@Law864.models_iff (Fin 8) (Magma.srch8R26 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R26_refutes_6 :
    FamilyRefutes Magma.srch8R26 [
      864
    ] :=
  noS8R26_Law864

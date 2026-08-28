import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 29 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 8,260 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 336 takes them (8260 nodes). -/
def ordS8R2_Law336 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 336. -/
theorem noS8R2_Law336 : ∀ v : Magma.tup8R2,
    ¬ @Equation336 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law336) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 2)
    (ord := ordS8R2_Law336) (by native_decide) v.1 v.2
    ((@Law336.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R2_refutes_28 :
    FamilyRefutes Magma.srch8R2 [
      336
    ] :=
  noS8R2_Law336

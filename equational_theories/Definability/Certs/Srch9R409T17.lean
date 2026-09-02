import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 18 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 11,041 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2875 takes them (11041 nodes). -/
def ordS9R409_Law2875 : List (Fin 12) := [2, 4, 1, 7, 6, 9, 0, 5, 11, 10, 8, 3]

/-- No member of the class satisfies equation 2875. -/
theorem noS9R409_Law2875 : ∀ v : Magma.tup9R409,
    ¬ @Equation2875 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 2)
    (ord := ordS9R409_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R409_refutes_17 :
    FamilyRefutes Magma.srch9R409 [
      2875
    ] :=
  noS9R409_Law2875

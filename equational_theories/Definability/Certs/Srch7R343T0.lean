import equational_theories.Definability.Srch_S7R343

/-!
# Structural certificate targets: `Magma.srch7R343` (part 1 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R343_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 62,148 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R343_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3352 takes them (62148 nodes). -/
def ordS7R343_Law3352 : List (Fin 19) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- No member of the class satisfies equation 3352. -/
theorem noS7R343_Law3352 : ∀ v : Magma.tup7R343,
    ¬ @Equation3352 (Fin 7) (Magma.srch7R343 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3352) (E := S7R343.E) (tr := S7R343.tr) (z := S7R343.z)
    (st := S7R343.st) (X := S7R343.X) (envs := Magma.envsRed 7 S7R343.E 2)
    (ord := ordS7R343_Law3352) (by native_decide) v.1 v.2
    ((@Law3352.models_iff (Fin 7) (Magma.srch7R343 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R343_refutes_0 :
    FamilyRefutes Magma.srch7R343 [
      3352
    ] :=
  noS7R343_Law3352

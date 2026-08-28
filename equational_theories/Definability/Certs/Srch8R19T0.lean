import equational_theories.Definability.Srch_S8R19

/-!
# Structural certificate targets: `Magma.srch8R19` (part 1 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R19_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 5,616 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R19_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3495 takes them (5616 nodes). -/
def ordS8R19_Law3495 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 3495. -/
theorem noS8R19_Law3495 : ∀ v : Magma.tup8R19,
    ¬ @Equation3495 (Fin 8) (Magma.srch8R19 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3495) (E := S8R19.E) (tr := S8R19.tr) (z := S8R19.z)
    (st := S8R19.st) (X := S8R19.X) (envs := Magma.envsRed 8 S8R19.E 3)
    (ord := ordS8R19_Law3495) (by native_decide) v.1 v.2
    ((@Law3495.models_iff (Fin 8) (Magma.srch8R19 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R19_refutes_0 :
    FamilyRefutes Magma.srch8R19 [
      3495
    ] :=
  noS8R19_Law3495

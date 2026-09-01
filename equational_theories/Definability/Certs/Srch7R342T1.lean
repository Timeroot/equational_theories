import equational_theories.Definability.Srch_S7R342

/-!
# Structural certificate targets: `Magma.srch7R342` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R342_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 19,673 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R342_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3919 takes them (19673 nodes). -/
def ordS7R342_Law3919 : List (Fin 19) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- No member of the class satisfies equation 3919. -/
theorem noS7R342_Law3919 : ∀ v : Magma.tup7R342,
    ¬ @Equation3919 (Fin 7) (Magma.srch7R342 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3919) (E := S7R342.E) (tr := S7R342.tr) (z := S7R342.z)
    (st := S7R342.st) (X := S7R342.X) (envs := Magma.envsRed 7 S7R342.E 3)
    (ord := ordS7R342_Law3919) (by native_decide) v.1 v.2
    ((@Law3919.models_iff (Fin 7) (Magma.srch7R342 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R342_refutes_1 :
    FamilyRefutes Magma.srch7R342 [
      3919
    ] :=
  noS7R342_Law3919

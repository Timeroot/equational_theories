import equational_theories.Definability.Srch_SR14

/-!
# Structural certificate targets: `Magma.srchR14` (part 3 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR14_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 364 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR14_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3868 takes them (364 nodes). -/
def ordSR14_Law3868 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3868. -/
theorem noSR14_Law3868 : ∀ v : Magma.tupR14,
    ¬ @Equation3868 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srchR14_refutes_2 :
    FamilyRefutes Magma.srchR14 [
      3868
    ] :=
  noSR14_Law3868

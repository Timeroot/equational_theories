import equational_theories.Definability.Srch_SR7

/-!
# Structural certificate targets: `Magma.srchR7` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR7_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 391 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR7_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3993 takes them (391 nodes). -/
def ordSR7_Law3993 : List (Fin 12) := [0, 10, 6, 4, 11, 3, 2, 1, 7, 8, 9, 5]

/-- No member of the class satisfies equation 3993. -/
theorem noSR7_Law3993 : ∀ v : Magma.tupR7,
    ¬ @Equation3993 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3993) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law3993) (by native_decide) v.1 v.2
    ((@Law3993.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srchR7_refutes_1 :
    FamilyRefutes Magma.srchR7 [
      3993
    ] :=
  noSR7_Law3993

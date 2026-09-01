import equational_theories.Definability.Srch_SR9

/-!
# Structural certificate targets: `Magma.srchR9` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 786 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4507 takes them (786 nodes). -/
def ordSR9_Law4507 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4507. -/
theorem noSR9_Law4507 : ∀ v : Magma.tupR9,
    ¬ @Equation4507 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4507) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law4507) (by native_decide) v.1 v.2
    ((@Law4507.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srchR9_refutes_1 :
    FamilyRefutes Magma.srchR9 [
      4507
    ] :=
  noSR9_Law4507

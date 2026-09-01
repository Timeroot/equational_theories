import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 23 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 6,063 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4075 takes them (6063 nodes). -/
def ordSR4_Law4075 : List (Fin 12) := [3, 10, 0, 8, 6, 9, 2, 11, 7, 4, 5, 1]

/-- No member of the class satisfies equation 4075. -/
theorem noSR4_Law4075 : ∀ v : Magma.tupR4,
    ¬ @Equation4075 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4075) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law4075) (by native_decide) v.1 v.2
    ((@Law4075.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srchR4_refutes_22 :
    FamilyRefutes Magma.srchR4 [
      4075
    ] :=
  noSR4_Law4075

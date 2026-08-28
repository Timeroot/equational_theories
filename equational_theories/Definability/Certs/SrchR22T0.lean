import equational_theories.Definability.Srch_SR22

/-!
# Structural certificate targets: `Magma.srchR22`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR22_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 78 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR22_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4358 takes them (43 nodes). -/
def ordSR22_Law4358 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4358. -/
theorem noSR22_Law4358 : ∀ v : Magma.tupR22,
    ¬ @Equation4358 (Fin 6) (Magma.srchR22 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := SR22.E) (tr := SR22.tr) (z := SR22.z)
    (st := SR22.st) (X := SR22.X) (envs := Magma.envsRed 6 SR22.E 3)
    (ord := ordSR22_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 6) (Magma.srchR22 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (35 nodes). -/
def ordSR22_Law4677 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4677. -/
theorem noSR22_Law4677 : ∀ v : Magma.tupR22,
    ¬ @Equation4677 (Fin 6) (Magma.srchR22 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := SR22.E) (tr := SR22.tr) (z := SR22.z)
    (st := SR22.st) (X := SR22.X) (envs := Magma.envsRed 6 SR22.E 3)
    (ord := ordSR22_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 6) (Magma.srchR22 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR22_refutes_0 :
    FamilyRefutes Magma.srchR22 [
      4358, 4677
    ] :=
  ⟨noSR22_Law4358, noSR22_Law4677⟩

import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 11 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 2,823 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3284 takes them (1379 nodes). -/
def ordSR4_Law3284 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3284. -/
theorem noSR4_Law3284 : ∀ v : Magma.tupR4,
    ¬ @Equation3284 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3284) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3284) (by native_decide) v.1 v.2
    ((@Law3284.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3292 takes them (1444 nodes). -/
def ordSR4_Law3292 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3292. -/
theorem noSR4_Law3292 : ∀ v : Magma.tupR4,
    ¬ @Equation3292 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3292) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3292) (by native_decide) v.1 v.2
    ((@Law3292.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR4_refutes_10 :
    FamilyRefutes Magma.srchR4 [
      3284, 3292
    ] :=
  ⟨noSR4_Law3284, noSR4_Law3292⟩

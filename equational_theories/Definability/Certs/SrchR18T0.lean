import equational_theories.Definability.Srch_SR18

/-!
# Structural certificate targets: `Magma.srchR18`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR18_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 617 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR18_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1457 takes them (297 nodes). -/
def ordSR18_Law1457 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1457. -/
theorem noSR18_Law1457 : ∀ v : Magma.tupR18,
    ¬ @Equation1457 (Fin 6) (Magma.srchR18 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1457) (E := SR18.E) (tr := SR18.tr) (z := SR18.z)
    (st := SR18.st) (X := SR18.X) (envs := Magma.envsRed 6 SR18.E 3)
    (ord := ordSR18_Law1457) (by native_decide) v.1 v.2
    ((@Law1457.models_iff (Fin 6) (Magma.srchR18 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2078 takes them (320 nodes). -/
def ordSR18_Law2078 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2078. -/
theorem noSR18_Law2078 : ∀ v : Magma.tupR18,
    ¬ @Equation2078 (Fin 6) (Magma.srchR18 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2078) (E := SR18.E) (tr := SR18.tr) (z := SR18.z)
    (st := SR18.st) (X := SR18.X) (envs := Magma.envsRed 6 SR18.E 3)
    (ord := ordSR18_Law2078) (by native_decide) v.1 v.2
    ((@Law2078.models_iff (Fin 6) (Magma.srchR18 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR18_refutes_0 :
    FamilyRefutes Magma.srchR18 [
      1457, 2078
    ] :=
  ⟨noSR18_Law1457, noSR18_Law2078⟩

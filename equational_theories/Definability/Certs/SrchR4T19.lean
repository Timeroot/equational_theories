import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 20 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 2,890 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3617 takes them (2638 nodes). -/
def ordSR4_Law3617 : List (Fin 12) := [3, 9, 5, 1, 11, 6, 7, 2, 4, 0, 10, 8]

/-- No member of the class satisfies equation 3617. -/
theorem noSR4_Law3617 : ∀ v : Magma.tupR4,
    ¬ @Equation3617 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3617) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3617) (by native_decide) v.1 v.2
    ((@Law3617.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3634 takes them (252 nodes). -/
def ordSR4_Law3634 : List (Fin 12) := [6, 9, 4, 11, 0, 10, 3, 8, 7, 1, 2, 5]

/-- No member of the class satisfies equation 3634. -/
theorem noSR4_Law3634 : ∀ v : Magma.tupR4,
    ¬ @Equation3634 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3634) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law3634) (by native_decide) v.1 v.2
    ((@Law3634.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR4_refutes_19 :
    FamilyRefutes Magma.srchR4 [
      3617, 3634
    ] :=
  ⟨noSR4_Law3617, noSR4_Law3634⟩

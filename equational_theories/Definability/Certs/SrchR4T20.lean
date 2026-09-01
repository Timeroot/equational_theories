import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 21 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,324 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3669 takes them (1225 nodes). -/
def ordSR4_Law3669 : List (Fin 12) := [4, 0, 6, 9, 8, 11, 3, 7, 5, 10, 2, 1]

/-- No member of the class satisfies equation 3669. -/
theorem noSR4_Law3669 : ∀ v : Magma.tupR4,
    ¬ @Equation3669 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3669) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3669) (by native_decide) v.1 v.2
    ((@Law3669.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3702 takes them (2099 nodes). -/
def ordSR4_Law3702 : List (Fin 12) := [5, 4, 7, 0, 3, 9, 11, 1, 2, 10, 6, 8]

/-- No member of the class satisfies equation 3702. -/
theorem noSR4_Law3702 : ∀ v : Magma.tupR4,
    ¬ @Equation3702 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3702) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3702) (by native_decide) v.1 v.2
    ((@Law3702.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR4_refutes_20 :
    FamilyRefutes Magma.srchR4 [
      3669, 3702
    ] :=
  ⟨noSR4_Law3669, noSR4_Law3702⟩

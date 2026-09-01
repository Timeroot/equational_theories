import equational_theories.Definability.Srch_SR12

/-!
# Structural certificate targets: `Magma.srchR12`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 254 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4437 takes them (102 nodes). -/
def ordSR12_Law4437 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4437. -/
theorem noSR12_Law4437 : ∀ v : Magma.tupR12,
    ¬ @Equation4437 (Fin 6) (Magma.srchR12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4437) (E := SR12.E) (tr := SR12.tr) (z := SR12.z)
    (st := SR12.st) (X := SR12.X) (envs := Magma.envsRed 6 SR12.E 3)
    (ord := ordSR12_Law4437) (by native_decide) v.1 v.2
    ((@Law4437.models_iff (Fin 6) (Magma.srchR12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4546 takes them (152 nodes). -/
def ordSR12_Law4546 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4546. -/
theorem noSR12_Law4546 : ∀ v : Magma.tupR12,
    ¬ @Equation4546 (Fin 6) (Magma.srchR12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4546) (E := SR12.E) (tr := SR12.tr) (z := SR12.z)
    (st := SR12.st) (X := SR12.X) (envs := Magma.envsRed 6 SR12.E 3)
    (ord := ordSR12_Law4546) (by native_decide) v.1 v.2
    ((@Law4546.models_iff (Fin 6) (Magma.srchR12 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR12_refutes_0 :
    FamilyRefutes Magma.srchR12 [
      4437, 4546
    ] :=
  ⟨noSR12_Law4437, noSR12_Law4546⟩

import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 17 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,836 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3461 takes them (2051 nodes). -/
def ordSR30_Law3461 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3461. -/
theorem noSR30_Law3461 : ∀ v : Magma.tupR30,
    ¬ @Equation3461 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3461) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law3461) (by native_decide) v.1 v.2
    ((@Law3461.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3512 takes them (1785 nodes). -/
def ordSR30_Law3512 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3512. -/
theorem noSR30_Law3512 : ∀ v : Magma.tupR30,
    ¬ @Equation3512 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3512) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law3512) (by native_decide) v.1 v.2
    ((@Law3512.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR30_refutes_16 :
    FamilyRefutes Magma.srchR30 [
      3461, 3512
    ] :=
  ⟨noSR30_Law3461, noSR30_Law3512⟩

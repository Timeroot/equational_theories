import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 26 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,749 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4284 takes them (2113 nodes). -/
def ordSR30_Law4284 : List (Fin 10) := [4, 5, 1, 7, 3, 8, 6, 0, 9, 2]

/-- No member of the class satisfies equation 4284. -/
theorem noSR30_Law4284 : ∀ v : Magma.tupR30,
    ¬ @Equation4284 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4284) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law4284) (by native_decide) v.1 v.2
    ((@Law4284.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4396 takes them (1636 nodes). -/
def ordSR30_Law4396 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4396. -/
theorem noSR30_Law4396 : ∀ v : Magma.tupR30,
    ¬ @Equation4396 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4396) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law4396) (by native_decide) v.1 v.2
    ((@Law4396.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR30_refutes_25 :
    FamilyRefutes Magma.srchR30 [
      4284, 4396
    ] :=
  ⟨noSR30_Law4284, noSR30_Law4396⟩

import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 3 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,715 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 378 takes them (2400 nodes). -/
def ordSR30_Law378 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 378. -/
theorem noSR30_Law378 : ∀ v : Magma.tupR30,
    ¬ @Equation378 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law378) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law378) (by native_decide) v.1 v.2
    ((@Law378.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 413 takes them (651 nodes). -/
def ordSR30_Law413 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 413. -/
theorem noSR30_Law413 : ∀ v : Magma.tupR30,
    ¬ @Equation413 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law413) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law413) (by native_decide) v.1 v.2
    ((@Law413.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (664 nodes). -/
def ordSR30_Law419 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 419. -/
theorem noSR30_Law419 : ∀ v : Magma.tupR30,
    ¬ @Equation419 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR30_refutes_2 :
    FamilyRefutes Magma.srchR30 [
      378, 413, 419
    ] :=
  ⟨noSR30_Law378, noSR30_Law413, noSR30_Law419⟩

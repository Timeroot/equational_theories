import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 37 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,170 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4512 takes them (2639 nodes). -/
def ordSR4_Law4512 : List (Fin 12) := [7, 8, 1, 9, 10, 5, 3, 4, 6, 0, 11, 2]

/-- No member of the class satisfies equation 4512. -/
theorem noSR4_Law4512 : ∀ v : Magma.tupR4,
    ¬ @Equation4512 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4512) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law4512) (by native_decide) v.1 v.2
    ((@Law4512.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4513 takes them (216 nodes). -/
def ordSR4_Law4513 : List (Fin 12) := [10, 9, 8, 5, 6, 4, 3, 1, 2, 7, 11, 0]

/-- No member of the class satisfies equation 4513. -/
theorem noSR4_Law4513 : ∀ v : Magma.tupR4,
    ¬ @Equation4513 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4513) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4513) (by native_decide) v.1 v.2
    ((@Law4513.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4564 takes them (315 nodes). -/
def ordSR4_Law4564 : List (Fin 12) := [3, 2, 11, 4, 6, 8, 9, 0, 7, 5, 10, 1]

/-- No member of the class satisfies equation 4564. -/
theorem noSR4_Law4564 : ∀ v : Magma.tupR4,
    ¬ @Equation4564 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4564) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4564) (by native_decide) v.1 v.2
    ((@Law4564.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR4_refutes_36 :
    FamilyRefutes Magma.srchR4 [
      4512, 4513, 4564
    ] :=
  ⟨noSR4_Law4512, noSR4_Law4513, noSR4_Law4564⟩

import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 15 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,161 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3367 takes them (1546 nodes). -/
def ordSR4_Law3367 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3367. -/
theorem noSR4_Law3367 : ∀ v : Magma.tupR4,
    ¬ @Equation3367 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3367) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3367) (by native_decide) v.1 v.2
    ((@Law3367.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3371 takes them (1135 nodes). -/
def ordSR4_Law3371 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3371. -/
theorem noSR4_Law3371 : ∀ v : Magma.tupR4,
    ¬ @Equation3371 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3371) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3371) (by native_decide) v.1 v.2
    ((@Law3371.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3375 takes them (480 nodes). -/
def ordSR4_Law3375 : List (Fin 12) := [10, 6, 0, 4, 7, 5, 8, 2, 1, 11, 3, 9]

/-- No member of the class satisfies equation 3375. -/
theorem noSR4_Law3375 : ∀ v : Magma.tupR4,
    ¬ @Equation3375 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3375) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law3375) (by native_decide) v.1 v.2
    ((@Law3375.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR4_refutes_14 :
    FamilyRefutes Magma.srchR4 [
      3367, 3371, 3375
    ] :=
  ⟨noSR4_Law3367, noSR4_Law3371, noSR4_Law3375⟩

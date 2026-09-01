import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 32 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,790 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4140 takes them (1844 nodes). -/
def ordSR4_Law4140 : List (Fin 12) := [6, 5, 8, 3, 1, 2, 10, 7, 9, 0, 4, 11]

/-- No member of the class satisfies equation 4140. -/
theorem noSR4_Law4140 : ∀ v : Magma.tupR4,
    ¬ @Equation4140 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4140) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4140) (by native_decide) v.1 v.2
    ((@Law4140.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4141 takes them (1568 nodes). -/
def ordSR4_Law4141 : List (Fin 12) := [9, 5, 11, 8, 10, 3, 0, 1, 6, 4, 2, 7]

/-- No member of the class satisfies equation 4141. -/
theorem noSR4_Law4141 : ∀ v : Magma.tupR4,
    ¬ @Equation4141 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4141) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law4141) (by native_decide) v.1 v.2
    ((@Law4141.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4144 takes them (378 nodes). -/
def ordSR4_Law4144 : List (Fin 12) := [5, 8, 6, 10, 0, 11, 9, 7, 2, 4, 1, 3]

/-- No member of the class satisfies equation 4144. -/
theorem noSR4_Law4144 : ∀ v : Magma.tupR4,
    ¬ @Equation4144 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4144) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4144) (by native_decide) v.1 v.2
    ((@Law4144.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR4_refutes_31 :
    FamilyRefutes Magma.srchR4 [
      4140, 4141, 4144
    ] :=
  ⟨noSR4_Law4140, noSR4_Law4141, noSR4_Law4144⟩

import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 25 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,329 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4078 takes them (1924 nodes). -/
def ordSR4_Law4078 : List (Fin 12) := [4, 5, 10, 0, 9, 7, 3, 6, 2, 11, 8, 1]

/-- No member of the class satisfies equation 4078. -/
theorem noSR4_Law4078 : ∀ v : Magma.tupR4,
    ¬ @Equation4078 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4078) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law4078) (by native_decide) v.1 v.2
    ((@Law4078.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4079 takes them (1405 nodes). -/
def ordSR4_Law4079 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4079. -/
theorem noSR4_Law4079 : ∀ v : Magma.tupR4,
    ¬ @Equation4079 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4079) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4079) (by native_decide) v.1 v.2
    ((@Law4079.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR4_refutes_24 :
    FamilyRefutes Magma.srchR4 [
      4078, 4079
    ] :=
  ⟨noSR4_Law4078, noSR4_Law4079⟩

import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 36 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 1,949 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4152 takes them (1744 nodes). -/
def ordSR4_Law4152 : List (Fin 12) := [10, 9, 7, 3, 8, 11, 4, 5, 0, 6, 2, 1]

/-- No member of the class satisfies equation 4152. -/
theorem noSR4_Law4152 : ∀ v : Magma.tupR4,
    ¬ @Equation4152 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4152) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4152) (by native_decide) v.1 v.2
    ((@Law4152.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4153 takes them (205 nodes). -/
def ordSR4_Law4153 : List (Fin 12) := [2, 4, 1, 3, 8, 11, 5, 0, 9, 10, 6, 7]

/-- No member of the class satisfies equation 4153. -/
theorem noSR4_Law4153 : ∀ v : Magma.tupR4,
    ¬ @Equation4153 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4153) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 5)
    (ord := ordSR4_Law4153) (by native_decide) v.1 v.2
    ((@Law4153.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR4_refutes_35 :
    FamilyRefutes Magma.srchR4 [
      4152, 4153
    ] :=
  ⟨noSR4_Law4152, noSR4_Law4153⟩

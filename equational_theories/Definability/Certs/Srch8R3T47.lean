import equational_theories.Definability.Srch_S8R3

/-!
# Structural certificate targets: `Magma.srch8R3` (part 48 of 77)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 796 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4367 takes them (401 nodes). -/
def ordS8R3_Law4367 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4367. -/
theorem noS8R3_Law4367 : ∀ v : Magma.tup8R3,
    ¬ @Equation4367 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4378 takes them (395 nodes). -/
def ordS8R3_Law4378 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4378. -/
theorem noS8R3_Law4378 : ∀ v : Magma.tup8R3,
    ¬ @Equation4378 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4378) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 5)
    (ord := ordS8R3_Law4378) (by native_decide) v.1 v.2
    ((@Law4378.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R3_refutes_47 :
    FamilyRefutes Magma.srch8R3 [
      4367, 4378
    ] :=
  ⟨noS8R3_Law4367, noS8R3_Law4378⟩

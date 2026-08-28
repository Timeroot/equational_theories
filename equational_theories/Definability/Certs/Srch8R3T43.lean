import equational_theories.Definability.Srch_S8R3

/-!
# Structural certificate targets: `Magma.srch8R3` (part 44 of 77)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,848 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4310 takes them (397 nodes). -/
def ordS8R3_Law4310 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4310. -/
theorem noS8R3_Law4310 : ∀ v : Magma.tup8R3,
    ¬ @Equation4310 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4323 takes them (3451 nodes). -/
def ordS8R3_Law4323 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4323. -/
theorem noS8R3_Law4323 : ∀ v : Magma.tup8R3,
    ¬ @Equation4323 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 3)
    (ord := ordS8R3_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R3_refutes_43 :
    FamilyRefutes Magma.srch8R3 [
      4310, 4323
    ] :=
  ⟨noS8R3_Law4310, noS8R3_Law4323⟩

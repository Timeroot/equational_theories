import equational_theories.Definability.Srch_S8R85

/-!
# Structural certificate targets: `Magma.srch8R85` (part 121 of 130)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R85_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 1,529 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R85_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4477 takes them (683 nodes). -/
def ordS8R85_Law4477 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4477. -/
theorem noS8R85_Law4477 : ∀ v : Magma.tup8R85,
    ¬ @Equation4477 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4477) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law4477) (by native_decide) v.1 v.2
    ((@Law4477.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4515 takes them (456 nodes). -/
def ordS8R85_Law4515 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4515. -/
theorem noS8R85_Law4515 : ∀ v : Magma.tup8R85,
    ¬ @Equation4515 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4515) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law4515) (by native_decide) v.1 v.2
    ((@Law4515.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4525 takes them (390 nodes). -/
def ordS8R85_Law4525 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4525. -/
theorem noS8R85_Law4525 : ∀ v : Magma.tup8R85,
    ¬ @Equation4525 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4525) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law4525) (by native_decide) v.1 v.2
    ((@Law4525.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R85_refutes_120 :
    FamilyRefutes Magma.srch8R85 [
      4477, 4515, 4525
    ] :=
  ⟨noS8R85_Law4477, noS8R85_Law4515, noS8R85_Law4525⟩

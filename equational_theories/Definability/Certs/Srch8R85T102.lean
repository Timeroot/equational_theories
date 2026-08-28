import equational_theories.Definability.Srch_S8R85

/-!
# Structural certificate targets: `Magma.srch8R85` (part 103 of 130)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R85_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 17,419 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R85_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4127 takes them (17419 nodes). -/
def ordS8R85_Law4127 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4127. -/
theorem noS8R85_Law4127 : ∀ v : Magma.tup8R85,
    ¬ @Equation4127 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 2)
    (ord := ordS8R85_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R85_refutes_102 :
    FamilyRefutes Magma.srch8R85 [
      4127
    ] :=
  noS8R85_Law4127

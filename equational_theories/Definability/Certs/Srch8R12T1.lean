import equational_theories.Definability.Srch_S8R12

/-!
# Structural certificate targets: `Magma.srch8R12` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,753 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1039 takes them (2753 nodes). -/
def ordS8R12_Law1039 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1039. -/
theorem noS8R12_Law1039 : ∀ v : Magma.tup8R12,
    ¬ @Equation1039 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 2)
    (ord := ordS8R12_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R12_refutes_1 :
    FamilyRefutes Magma.srch8R12 [
      1039
    ] :=
  noS8R12_Law1039

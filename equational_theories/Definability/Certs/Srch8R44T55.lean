import equational_theories.Definability.Srch_S8R44

/-!
# Structural certificate targets: `Magma.srch8R44` (part 56 of 64)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R44_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 9,547 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R44_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4138 takes them (9547 nodes). -/
def ordS8R44_Law4138 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4138. -/
theorem noS8R44_Law4138 : ∀ v : Magma.tup8R44,
    ¬ @Equation4138 (Fin 8) (Magma.srch8R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4138) (E := S8R44.E) (tr := S8R44.tr) (z := S8R44.z)
    (st := S8R44.st) (X := S8R44.X) (envs := Magma.envsRed 8 S8R44.E 3)
    (ord := ordS8R44_Law4138) (by native_decide) v.1 v.2
    ((@Law4138.models_iff (Fin 8) (Magma.srch8R44 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R44_refutes_55 :
    FamilyRefutes Magma.srch8R44 [
      4138
    ] :=
  noS8R44_Law4138

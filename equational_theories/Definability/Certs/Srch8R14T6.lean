import equational_theories.Definability.Srch_S8R14

/-!
# Structural certificate targets: `Magma.srch8R14` (part 7 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R14_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 10,906 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R14_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4074 takes them (10906 nodes). -/
def ordS8R14_Law4074 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4074. -/
theorem noS8R14_Law4074 : ∀ v : Magma.tup8R14,
    ¬ @Equation4074 (Fin 8) (Magma.srch8R14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S8R14.E) (tr := S8R14.tr) (z := S8R14.z)
    (st := S8R14.st) (X := S8R14.X) (envs := Magma.envsRed 8 S8R14.E 2)
    (ord := ordS8R14_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 8) (Magma.srch8R14 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R14_refutes_6 :
    FamilyRefutes Magma.srch8R14 [
      4074
    ] :=
  noS8R14_Law4074

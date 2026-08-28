import equational_theories.Definability.Srch_S8R36

/-!
# Structural certificate targets: `Magma.srch8R36` (part 4 of 12)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R36_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 17,321 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R36_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2457 takes them (17321 nodes). -/
def ordS8R36_Law2457 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R36_Law2457 : ∀ v : Magma.tup8R36,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R36 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R36.E) (tr := S8R36.tr) (z := S8R36.z)
    (st := S8R36.st) (X := S8R36.X) (envs := Magma.envsRed 8 S8R36.E 2)
    (ord := ordS8R36_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R36 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R36_refutes_3 :
    FamilyRefutes Magma.srch8R36 [
      2457
    ] :=
  noS8R36_Law2457

import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 9 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 1,892 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1253 takes them (1892 nodes). -/
def ordS8R46_Law1253 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1253. -/
theorem noS8R46_Law1253 : ∀ v : Magma.tup8R46,
    ¬ @Equation1253 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1253) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law1253) (by native_decide) v.1 v.2
    ((@Law1253.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R46_refutes_8 :
    FamilyRefutes Magma.srch8R46 [
      1253
    ] :=
  noS8R46_Law1253

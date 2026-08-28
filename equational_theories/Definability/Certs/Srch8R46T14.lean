import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 15 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,214 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1931 takes them (2214 nodes). -/
def ordS8R46_Law1931 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1931. -/
theorem noS8R46_Law1931 : ∀ v : Magma.tup8R46,
    ¬ @Equation1931 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1931) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 2)
    (ord := ordS8R46_Law1931) (by native_decide) v.1 v.2
    ((@Law1931.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R46_refutes_14 :
    FamilyRefutes Magma.srch8R46 [
      1931
    ] :=
  noS8R46_Law1931

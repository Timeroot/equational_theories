import equational_theories.Definability.Srch_S8R406

/-!
# Structural certificate targets: `Magma.srch8R406` (part 5 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R406_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 15,822 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R406_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1898 takes them (15822 nodes). -/
def ordS8R406_Law1898 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1898. -/
theorem noS8R406_Law1898 : ∀ v : Magma.tup8R406,
    ¬ @Equation1898 (Fin 8) (Magma.srch8R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1898) (E := S8R406.E) (tr := S8R406.tr) (z := S8R406.z)
    (st := S8R406.st) (X := S8R406.X) (envs := Magma.envsRed 8 S8R406.E 2)
    (ord := ordS8R406_Law1898) (by native_decide) v.1 v.2
    ((@Law1898.models_iff (Fin 8) (Magma.srch8R406 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch8R406_refutes_4 :
    FamilyRefutes Magma.srch8R406 [
      1898
    ] :=
  noS8R406_Law1898

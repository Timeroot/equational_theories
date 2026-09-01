import equational_theories.Definability.Srch_S7R305

/-!
# Structural certificate targets: `Magma.srch7R305` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R305_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 58,686 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R305_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3865 takes them (58686 nodes). -/
def ordS7R305_Law3865 : List (Fin 14) := [0, 5, 2, 3, 6, 10, 8, 1, 7, 4, 13, 12, 11, 9]

/-- No member of the class satisfies equation 3865. -/
theorem noS7R305_Law3865 : ∀ v : Magma.tup7R305,
    ¬ @Equation3865 (Fin 7) (Magma.srch7R305 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S7R305.E) (tr := S7R305.tr) (z := S7R305.z)
    (st := S7R305.st) (X := S7R305.X) (envs := Magma.envsRed 7 S7R305.E 2)
    (ord := ordS7R305_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 7) (Magma.srch7R305 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R305_refutes_1 :
    FamilyRefutes Magma.srch7R305 [
      3865
    ] :=
  noS7R305_Law3865

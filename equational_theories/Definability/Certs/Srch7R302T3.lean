import equational_theories.Definability.Srch_S7R302

/-!
# Structural certificate targets: `Magma.srch7R302` (part 4 of 13)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R302_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 3,936 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R302_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1724 takes them (3936 nodes). -/
def ordS7R302_Law1724 : List (Fin 15) := [13, 0, 14, 8, 1, 12, 6, 4, 11, 9, 2, 10, 7, 5, 3]

/-- No member of the class satisfies equation 1724. -/
theorem noS7R302_Law1724 : ∀ v : Magma.tup7R302,
    ¬ @Equation1724 (Fin 7) (Magma.srch7R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1724) (E := S7R302.E) (tr := S7R302.tr) (z := S7R302.z)
    (st := S7R302.st) (X := S7R302.X) (envs := Magma.envsRed 7 S7R302.E 3)
    (ord := ordS7R302_Law1724) (by native_decide) v.1 v.2
    ((@Law1724.models_iff (Fin 7) (Magma.srch7R302 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R302_refutes_3 :
    FamilyRefutes Magma.srch7R302 [
      1724
    ] :=
  noS7R302_Law1724

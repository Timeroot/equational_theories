import equational_theories.Definability.Srch_S7R302

/-!
# Structural certificate targets: `Magma.srch7R302` (part 13 of 13)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R302_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 117,166 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R302_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4071 takes them (117166 nodes). -/
def ordS7R302_Law4071 : List (Fin 15) := [11, 7, 0, 3, 13, 1, 12, 6, 4, 14, 9, 10, 8, 5, 2]

/-- No member of the class satisfies equation 4071. -/
theorem noS7R302_Law4071 : ∀ v : Magma.tup7R302,
    ¬ @Equation4071 (Fin 7) (Magma.srch7R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S7R302.E) (tr := S7R302.tr) (z := S7R302.z)
    (st := S7R302.st) (X := S7R302.X) (envs := Magma.envsRed 7 S7R302.E 2)
    (ord := ordS7R302_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 7) (Magma.srch7R302 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R302_refutes_12 :
    FamilyRefutes Magma.srch7R302 [
      4071
    ] :=
  noS7R302_Law4071

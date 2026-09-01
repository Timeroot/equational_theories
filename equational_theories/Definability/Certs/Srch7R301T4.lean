import equational_theories.Definability.Srch_S7R301

/-!
# Structural certificate targets: `Magma.srch7R301` (part 5 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R301_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 4,646 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R301_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1119 takes them (4646 nodes). -/
def ordS7R301_Law1119 : List (Fin 9) := [0, 1, 5, 7, 4, 8, 3, 6, 2]

/-- No member of the class satisfies equation 1119. -/
theorem noS7R301_Law1119 : ∀ v : Magma.tup7R301,
    ¬ @Equation1119 (Fin 7) (Magma.srch7R301 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1119) (E := S7R301.E) (tr := S7R301.tr) (z := S7R301.z)
    (st := S7R301.st) (X := S7R301.X) (envs := Magma.envsRed 7 S7R301.E 2)
    (ord := ordS7R301_Law1119) (by native_decide) v.1 v.2
    ((@Law1119.models_iff (Fin 7) (Magma.srch7R301 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R301_refutes_4 :
    FamilyRefutes Magma.srch7R301 [
      1119
    ] :=
  noS7R301_Law1119

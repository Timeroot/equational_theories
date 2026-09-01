import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 20 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 22,078 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4586 takes them (22078 nodes). -/
def ordS7R325_Law4586 : List (Fin 9) := [0, 7, 4, 1, 6, 8, 3, 2, 5]

/-- No member of the class satisfies equation 4586. -/
theorem noS7R325_Law4586 : ∀ v : Magma.tup7R325,
    ¬ @Equation4586 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4586) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4586) (by native_decide) v.1 v.2
    ((@Law4586.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R325_refutes_19 :
    FamilyRefutes Magma.srch7R325 [
      4586
    ] :=
  noS7R325_Law4586

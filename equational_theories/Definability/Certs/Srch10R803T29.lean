import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 30 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,053 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4598 takes them (2053 nodes). -/
def ordS10R803_Law4598 : List (Fin 8) := [1, 7, 3, 4, 0, 6, 5, 2]

/-- No member of the class satisfies equation 4598. -/
theorem noS10R803_Law4598 : ∀ v : Magma.tup10R803,
    ¬ @Equation4598 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4598) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4598) (by native_decide) v.1 v.2
    ((@Law4598.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch10R803_refutes_29 :
    FamilyRefutes Magma.srch10R803 [
      4598
    ] :=
  noS10R803_Law4598

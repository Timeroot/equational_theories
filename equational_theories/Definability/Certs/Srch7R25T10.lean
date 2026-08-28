import equational_theories.Definability.Srch_S7R25

/-!
# Structural certificate targets: `Magma.srch7R25` (part 11 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 2,384 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3955 takes them (2384 nodes). -/
def ordS7R25_Law3955 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3955. -/
theorem noS7R25_Law3955 : ∀ v : Magma.tup7R25,
    ¬ @Equation3955 (Fin 7) (Magma.srch7R25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S7R25.E) (tr := S7R25.tr) (z := S7R25.z)
    (st := S7R25.st) (X := S7R25.X) (envs := Magma.envsRed 7 S7R25.E 2)
    (ord := ordS7R25_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 7) (Magma.srch7R25 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R25_refutes_10 :
    FamilyRefutes Magma.srch7R25 [
      3955
    ] :=
  noS7R25_Law3955

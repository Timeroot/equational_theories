import equational_theories.Definability.Srch_S7R5

/-!
# Structural certificate targets: `Magma.srch7R5` (part 3 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R5_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `1`
equations here, 5,095 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R5_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 872 takes them (5095 nodes). -/
def ordS7R5_Law872 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 872. -/
theorem noS7R5_Law872 : ∀ v : Magma.tup7R5,
    ¬ @Equation872 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 2)
    (ord := ordS7R5_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R5_refutes_2 :
    FamilyRefutes Magma.srch7R5 [
      872
    ] :=
  noS7R5_Law872

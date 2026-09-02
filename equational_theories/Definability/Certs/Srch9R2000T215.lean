import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 216 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 7,000 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4137 takes them (7000 nodes). -/
def ordS9R2000_Law4137 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4137. -/
theorem noS9R2000_Law4137 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4137 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4137) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law4137) (by native_decide) v.1 v.2
    ((@Law4137.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch9R2000_refutes_215 :
    FamilyRefutes Magma.srch9R2000 [
      4137
    ] :=
  noS9R2000_Law4137

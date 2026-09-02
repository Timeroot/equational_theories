import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 146 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,123 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2491 takes them (3081 nodes). -/
def ordS9R2000_Law2491 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2491. -/
theorem noS9R2000_Law2491 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2491 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2491) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2491) (by native_decide) v.1 v.2
    ((@Law2491.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2492 takes them (42 nodes). -/
def ordS9R2000_Law2492 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2492. -/
theorem noS9R2000_Law2492 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2492 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2492) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law2492) (by native_decide) v.1 v.2
    ((@Law2492.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R2000_refutes_145 :
    FamilyRefutes Magma.srch9R2000 [
      2491, 2492
    ] :=
  ⟨noS9R2000_Law2491, noS9R2000_Law2492⟩

import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 9 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,134 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 860 takes them (1447 nodes). -/
def ordS9R409_Law860 : List (Fin 12) := [7, 4, 3, 9, 2, 6, 8, 0, 5, 1, 10, 11]

/-- No member of the class satisfies equation 860. -/
theorem noS9R409_Law860 : ∀ v : Magma.tup9R409,
    ¬ @Equation860 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law860) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law860) (by native_decide) v.1 v.2
    ((@Law860.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 864 takes them (687 nodes). -/
def ordS9R409_Law864 : List (Fin 12) := [7, 4, 3, 9, 0, 2, 6, 8, 1, 11, 10, 5]

/-- No member of the class satisfies equation 864. -/
theorem noS9R409_Law864 : ∀ v : Magma.tup9R409,
    ¬ @Equation864 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law864) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law864) (by native_decide) v.1 v.2
    ((@Law864.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R409_refutes_8 :
    FamilyRefutes Magma.srch9R409 [
      860, 864
    ] :=
  ⟨noS9R409_Law860, noS9R409_Law864⟩

import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 20 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,672 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3061 takes them (1626 nodes). -/
def ordS9R409_Law3061 : List (Fin 12) := [6, 2, 5, 7, 10, 11, 9, 8, 4, 3, 0, 1]

/-- No member of the class satisfies equation 3061. -/
theorem noS9R409_Law3061 : ∀ v : Magma.tup9R409,
    ¬ @Equation3061 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3061) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law3061) (by native_decide) v.1 v.2
    ((@Law3061.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3081 takes them (2046 nodes). -/
def ordS9R409_Law3081 : List (Fin 12) := [1, 11, 4, 3, 6, 7, 10, 5, 9, 0, 2, 8]

/-- No member of the class satisfies equation 3081. -/
theorem noS9R409_Law3081 : ∀ v : Magma.tup9R409,
    ¬ @Equation3081 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3081) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law3081) (by native_decide) v.1 v.2
    ((@Law3081.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R409_refutes_19 :
    FamilyRefutes Magma.srch9R409 [
      3061, 3081
    ] :=
  ⟨noS9R409_Law3061, noS9R409_Law3081⟩

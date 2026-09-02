import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 16 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,174 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2683 takes them (1976 nodes). -/
def ordS9R409_Law2683 : List (Fin 12) := [4, 6, 9, 1, 3, 8, 5, 11, 2, 10, 0, 7]

/-- No member of the class satisfies equation 2683. -/
theorem noS9R409_Law2683 : ∀ v : Magma.tup9R409,
    ¬ @Equation2683 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2683) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2683) (by native_decide) v.1 v.2
    ((@Law2683.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2691 takes them (577 nodes). -/
def ordS9R409_Law2691 : List (Fin 12) := [2, 7, 10, 9, 8, 4, 11, 0, 5, 6, 3, 1]

/-- No member of the class satisfies equation 2691. -/
theorem noS9R409_Law2691 : ∀ v : Magma.tup9R409,
    ¬ @Equation2691 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2691) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law2691) (by native_decide) v.1 v.2
    ((@Law2691.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2858 takes them (621 nodes). -/
def ordS9R409_Law2858 : List (Fin 12) := [9, 6, 10, 4, 3, 8, 0, 5, 2, 1, 11, 7]

/-- No member of the class satisfies equation 2858. -/
theorem noS9R409_Law2858 : ∀ v : Magma.tup9R409,
    ¬ @Equation2858 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2858) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2858) (by native_decide) v.1 v.2
    ((@Law2858.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R409_refutes_15 :
    FamilyRefutes Magma.srch9R409 [
      2683, 2691, 2858
    ] :=
  ⟨noS9R409_Law2683, noS9R409_Law2691, noS9R409_Law2858⟩

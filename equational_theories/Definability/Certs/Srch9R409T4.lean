import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 5 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,719 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 454 takes them (1712 nodes). -/
def ordS9R409_Law454 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 454. -/
theorem noS9R409_Law454 : ∀ v : Magma.tup9R409,
    ¬ @Equation454 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law454) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law454) (by native_decide) v.1 v.2
    ((@Law454.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 458 takes them (966 nodes). -/
def ordS9R409_Law458 : List (Fin 12) := [4, 10, 6, 9, 7, 0, 3, 2, 8, 11, 1, 5]

/-- No member of the class satisfies equation 458. -/
theorem noS9R409_Law458 : ∀ v : Magma.tup9R409,
    ¬ @Equation458 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law458) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law458) (by native_decide) v.1 v.2
    ((@Law458.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 635 takes them (1041 nodes). -/
def ordS9R409_Law635 : List (Fin 12) := [4, 10, 9, 2, 11, 8, 0, 7, 5, 3, 1, 6]

/-- No member of the class satisfies equation 635. -/
theorem noS9R409_Law635 : ∀ v : Magma.tup9R409,
    ¬ @Equation635 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law635) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law635) (by native_decide) v.1 v.2
    ((@Law635.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R409_refutes_4 :
    FamilyRefutes Magma.srch9R409 [
      454, 458, 635
    ] :=
  ⟨noS9R409_Law454, noS9R409_Law458, noS9R409_Law635⟩

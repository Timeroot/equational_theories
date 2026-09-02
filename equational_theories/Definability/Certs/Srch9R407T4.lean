import equational_theories.Definability.Srch_S9R407

/-!
# Structural certificate targets: `Magma.srch9R407` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R407_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 461 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R407_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4645 takes them (219 nodes). -/
def ordS9R407_Law4645 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4645. -/
theorem noS9R407_Law4645 : ∀ v : Magma.tup9R407,
    ¬ @Equation4645 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (76 nodes). -/
def ordS9R407_Law4677 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4677. -/
theorem noS9R407_Law4677 : ∀ v : Magma.tup9R407,
    ¬ @Equation4677 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (166 nodes). -/
def ordS9R407_Law4689 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4689. -/
theorem noS9R407_Law4689 : ∀ v : Magma.tup9R407,
    ¬ @Equation4689 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R407_refutes_4 :
    FamilyRefutes Magma.srch9R407 [
      4645, 4677, 4689
    ] :=
  ⟨noS9R407_Law4645, noS9R407_Law4677, noS9R407_Law4689⟩

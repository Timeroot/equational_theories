import equational_theories.Definability.Srch_S9R405

/-!
# Structural certificate targets: `Magma.srch9R405` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R405_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,190 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R405_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3271 takes them (689 nodes). -/
def ordS9R405_Law3271 : List (Fin 9) := [8, 6, 4, 5, 2, 0, 1, 3, 7]

/-- No member of the class satisfies equation 3271. -/
theorem noS9R405_Law3271 : ∀ v : Magma.tup9R405,
    ¬ @Equation3271 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3271) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3271) (by native_decide) v.1 v.2
    ((@Law3271.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (598 nodes). -/
def ordS9R405_Law3474 : List (Fin 9) := [6, 5, 2, 0, 4, 1, 7, 3, 8]

/-- No member of the class satisfies equation 3474. -/
theorem noS9R405_Law3474 : ∀ v : Magma.tup9R405,
    ¬ @Equation3474 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (392 nodes). -/
def ordS9R405_Law3481 : List (Fin 9) := [7, 5, 0, 8, 6, 3, 1, 4, 2]

/-- No member of the class satisfies equation 3481. -/
theorem noS9R405_Law3481 : ∀ v : Magma.tup9R405,
    ¬ @Equation3481 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3667 takes them (1511 nodes). -/
def ordS9R405_Law3667 : List (Fin 9) := [8, 5, 0, 3, 6, 2, 4, 7, 1]

/-- No member of the class satisfies equation 3667. -/
theorem noS9R405_Law3667 : ∀ v : Magma.tup9R405,
    ¬ @Equation3667 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3667) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3667) (by native_decide) v.1 v.2
    ((@Law3667.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch9R405_refutes_0 :
    FamilyRefutes Magma.srch9R405 [
      3271, 3474, 3481, 3667
    ] :=
  ⟨noS9R405_Law3271, noS9R405_Law3474, noS9R405_Law3481, noS9R405_Law3667⟩

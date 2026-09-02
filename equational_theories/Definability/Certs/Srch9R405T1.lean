import equational_theories.Definability.Srch_S9R405

/-!
# Structural certificate targets: `Magma.srch9R405` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R405_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 1,751 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R405_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3865 takes them (833 nodes). -/
def ordS9R405_Law3865 : List (Fin 9) := [4, 1, 5, 6, 8, 2, 0, 7, 3]

/-- No member of the class satisfies equation 3865. -/
theorem noS9R405_Law3865 : ∀ v : Magma.tup9R405,
    ¬ @Equation3865 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3868 takes them (257 nodes). -/
def ordS9R405_Law3868 : List (Fin 9) := [0, 3, 6, 4, 5, 1, 8, 7, 2]

/-- No member of the class satisfies equation 3868. -/
theorem noS9R405_Law3868 : ∀ v : Magma.tup9R405,
    ¬ @Equation3868 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4071 takes them (661 nodes). -/
def ordS9R405_Law4071 : List (Fin 9) := [2, 5, 0, 6, 7, 8, 3, 4, 1]

/-- No member of the class satisfies equation 4071. -/
theorem noS9R405_Law4071 : ∀ v : Magma.tup9R405,
    ¬ @Equation4071 (Fin 9) (Magma.srch9R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S9R405.E) (tr := S9R405.tr) (z := S9R405.z)
    (st := S9R405.st) (X := S9R405.X) (envs := Magma.envsRed 9 S9R405.E 2)
    (ord := ordS9R405_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 9) (Magma.srch9R405 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R405_refutes_1 :
    FamilyRefutes Magma.srch9R405 [
      3865, 3868, 4071
    ] :=
  ⟨noS9R405_Law3865, noS9R405_Law3868, noS9R405_Law4071⟩

import equational_theories.Definability.Srch_S9R317

/-!
# Structural certificate targets: `Magma.srch9R317`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R317_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 24 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R317_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 422 takes them (6 nodes). -/
def ordS9R317_Law422 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 422. -/
theorem noS9R317_Law422 : ∀ v : Magma.tup9R317,
    ¬ @Equation422 (Fin 9) (Magma.srch9R317 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law422) (E := S9R317.E) (tr := S9R317.tr) (z := S9R317.z)
    (st := S9R317.st) (X := S9R317.X) (envs := Magma.envsRed 9 S9R317.E 3)
    (ord := ordS9R317_Law422) (by native_decide) v.1 v.2
    ((@Law422.models_iff (Fin 9) (Magma.srch9R317 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 828 takes them (6 nodes). -/
def ordS9R317_Law828 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 828. -/
theorem noS9R317_Law828 : ∀ v : Magma.tup9R317,
    ¬ @Equation828 (Fin 9) (Magma.srch9R317 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law828) (E := S9R317.E) (tr := S9R317.tr) (z := S9R317.z)
    (st := S9R317.st) (X := S9R317.X) (envs := Magma.envsRed 9 S9R317.E 3)
    (ord := ordS9R317_Law828) (by native_decide) v.1 v.2
    ((@Law828.models_iff (Fin 9) (Magma.srch9R317 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (6 nodes). -/
def ordS9R317_Law2679 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2679. -/
theorem noS9R317_Law2679 : ∀ v : Magma.tup9R317,
    ¬ @Equation2679 (Fin 9) (Magma.srch9R317 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S9R317.E) (tr := S9R317.tr) (z := S9R317.z)
    (st := S9R317.st) (X := S9R317.X) (envs := Magma.envsRed 9 S9R317.E 3)
    (ord := ordS9R317_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 9) (Magma.srch9R317 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3085 takes them (6 nodes). -/
def ordS9R317_Law3085 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3085. -/
theorem noS9R317_Law3085 : ∀ v : Magma.tup9R317,
    ¬ @Equation3085 (Fin 9) (Magma.srch9R317 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3085) (E := S9R317.E) (tr := S9R317.tr) (z := S9R317.z)
    (st := S9R317.st) (X := S9R317.X) (envs := Magma.envsRed 9 S9R317.E 3)
    (ord := ordS9R317_Law3085) (by native_decide) v.1 v.2
    ((@Law3085.models_iff (Fin 9) (Magma.srch9R317 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch9R317_refutes_0 :
    FamilyRefutes Magma.srch9R317 [
      422, 828, 2679, 3085
    ] :=
  ⟨noS9R317_Law422, noS9R317_Law828, noS9R317_Law2679, noS9R317_Law3085⟩

import equational_theories.Definability.Srch_S9R403

/-!
# Structural certificate targets: `Magma.srch9R403` (part 4 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R403_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 1,428 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R403_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3414 takes them (201 nodes). -/
def ordS9R403_Law3414 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3414. -/
theorem noS9R403_Law3414 : ∀ v : Magma.tup9R403,
    ¬ @Equation3414 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (294 nodes). -/
def ordS9R403_Law3526 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3526. -/
theorem noS9R403_Law3526 : ∀ v : Magma.tup9R403,
    ¬ @Equation3526 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (357 nodes). -/
def ordS9R403_Law4023 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4023. -/
theorem noS9R403_Law4023 : ∀ v : Magma.tup9R403,
    ¬ @Equation4023 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (322 nodes). -/
def ordS9R403_Law4135 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4135. -/
theorem noS9R403_Law4135 : ∀ v : Magma.tup9R403,
    ¬ @Equation4135 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (254 nodes). -/
def ordS9R403_Law4146 : List (Fin 7) := [4, 3, 2, 5, 0, 6, 1]

/-- No member of the class satisfies equation 4146. -/
theorem noS9R403_Law4146 : ∀ v : Magma.tup9R403,
    ¬ @Equation4146 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch9R403_refutes_3 :
    FamilyRefutes Magma.srch9R403 [
      3414, 3526, 4023, 4135, 4146
    ] :=
  ⟨noS9R403_Law3414, noS9R403_Law3526, noS9R403_Law4023, noS9R403_Law4135, noS9R403_Law4146⟩

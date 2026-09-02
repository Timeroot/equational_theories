import equational_theories.Definability.Srch_S9R407

/-!
# Structural certificate targets: `Magma.srch9R407` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R407_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 3,179 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R407_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3955 takes them (307 nodes). -/
def ordS9R407_Law3955 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3955. -/
theorem noS9R407_Law3955 : ∀ v : Magma.tup9R407,
    ¬ @Equation3955 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (292 nodes). -/
def ordS9R407_Law4130 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4130. -/
theorem noS9R407_Law4130 : ∀ v : Magma.tup9R407,
    ¬ @Equation4130 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (358 nodes). -/
def ordS9R407_Law4135 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4135. -/
theorem noS9R407_Law4135 : ∀ v : Magma.tup9R407,
    ¬ @Equation4135 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4175 takes them (238 nodes). -/
def ordS9R407_Law4175 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4175. -/
theorem noS9R407_Law4175 : ∀ v : Magma.tup9R407,
    ¬ @Equation4175 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4175) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4175) (by native_decide) v.1 v.2
    ((@Law4175.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (225 nodes). -/
def ordS9R407_Law4283 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4283. -/
theorem noS9R407_Law4283 : ∀ v : Magma.tup9R407,
    ¬ @Equation4283 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4286 takes them (91 nodes). -/
def ordS9R407_Law4286 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4286. -/
theorem noS9R407_Law4286 : ∀ v : Magma.tup9R407,
    ¬ @Equation4286 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4286) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4286) (by native_decide) v.1 v.2
    ((@Law4286.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (146 nodes). -/
def ordS9R407_Law4291 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4291. -/
theorem noS9R407_Law4291 : ∀ v : Magma.tup9R407,
    ¬ @Equation4291 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (175 nodes). -/
def ordS9R407_Law4315 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4315. -/
theorem noS9R407_Law4315 : ∀ v : Magma.tup9R407,
    ¬ @Equation4315 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (296 nodes). -/
def ordS9R407_Law4339 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4339. -/
theorem noS9R407_Law4339 : ∀ v : Magma.tup9R407,
    ¬ @Equation4339 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (138 nodes). -/
def ordS9R407_Law4357 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4357. -/
theorem noS9R407_Law4357 : ∀ v : Magma.tup9R407,
    ¬ @Equation4357 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (88 nodes). -/
def ordS9R407_Law4358 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4358. -/
theorem noS9R407_Law4358 : ∀ v : Magma.tup9R407,
    ¬ @Equation4358 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4405 takes them (70 nodes). -/
def ordS9R407_Law4405 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4405. -/
theorem noS9R407_Law4405 : ∀ v : Magma.tup9R407,
    ¬ @Equation4405 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4405) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4405) (by native_decide) v.1 v.2
    ((@Law4405.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4438 takes them (146 nodes). -/
def ordS9R407_Law4438 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4438. -/
theorem noS9R407_Law4438 : ∀ v : Magma.tup9R407,
    ¬ @Equation4438 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4438) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4438) (by native_decide) v.1 v.2
    ((@Law4438.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4615 takes them (118 nodes). -/
def ordS9R407_Law4615 : List (Fin 7) := [5, 2, 6, 0, 1, 3, 4]

/-- No member of the class satisfies equation 4615. -/
theorem noS9R407_Law4615 : ∀ v : Magma.tup9R407,
    ¬ @Equation4615 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4615) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4615) (by native_decide) v.1 v.2
    ((@Law4615.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (154 nodes). -/
def ordS9R407_Law4629 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4629. -/
theorem noS9R407_Law4629 : ∀ v : Magma.tup9R407,
    ¬ @Equation4629 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (225 nodes). -/
def ordS9R407_Law4635 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4635. -/
theorem noS9R407_Law4635 : ∀ v : Magma.tup9R407,
    ¬ @Equation4635 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4642 takes them (112 nodes). -/
def ordS9R407_Law4642 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4642. -/
theorem noS9R407_Law4642 : ∀ v : Magma.tup9R407,
    ¬ @Equation4642 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4642) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law4642) (by native_decide) v.1 v.2
    ((@Law4642.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch9R407_refutes_3 :
    FamilyRefutes Magma.srch9R407 [
      3955, 4130, 4135, 4175, 4283, 4286, 4291, 4315, 4339, 4357, 4358, 4405, 4438, 4615, 4629,
      4635, 4642
    ] :=
  ⟨noS9R407_Law3955, noS9R407_Law4130, noS9R407_Law4135, noS9R407_Law4175, noS9R407_Law4283, noS9R407_Law4286, noS9R407_Law4291, noS9R407_Law4315, noS9R407_Law4339, noS9R407_Law4357, noS9R407_Law4358, noS9R407_Law4405, noS9R407_Law4438, noS9R407_Law4615, noS9R407_Law4629, noS9R407_Law4635, noS9R407_Law4642⟩

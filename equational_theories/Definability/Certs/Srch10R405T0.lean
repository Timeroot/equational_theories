import equational_theories.Definability.Srch_S10R405

/-!
# Structural certificate targets: `Magma.srch10R405`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R405_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 242 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R405_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3308 takes them (29 nodes). -/
def ordS10R405_Law3308 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3308. -/
theorem noS10R405_Law3308 : ∀ v : Magma.tup10R405,
    ¬ @Equation3308 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (17 nodes). -/
def ordS10R405_Law3343 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3343. -/
theorem noS10R405_Law3343 : ∀ v : Magma.tup10R405,
    ¬ @Equation3343 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (29 nodes). -/
def ordS10R405_Law3511 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3511. -/
theorem noS10R405_Law3511 : ∀ v : Magma.tup10R405,
    ¬ @Equation3511 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (29 nodes). -/
def ordS10R405_Law3955 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3955. -/
theorem noS10R405_Law3955 : ∀ v : Magma.tup10R405,
    ¬ @Equation3955 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (17 nodes). -/
def ordS10R405_Law4130 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4130. -/
theorem noS10R405_Law4130 : ∀ v : Magma.tup10R405,
    ¬ @Equation4130 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (29 nodes). -/
def ordS10R405_Law4158 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4158. -/
theorem noS10R405_Law4158 : ∀ v : Magma.tup10R405,
    ¬ @Equation4158 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (23 nodes). -/
def ordS10R405_Law4283 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4283. -/
theorem noS10R405_Law4283 : ∀ v : Magma.tup10R405,
    ¬ @Equation4283 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (23 nodes). -/
def ordS10R405_Law4291 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4291. -/
theorem noS10R405_Law4291 : ∀ v : Magma.tup10R405,
    ¬ @Equation4291 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (23 nodes). -/
def ordS10R405_Law4629 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4629. -/
theorem noS10R405_Law4629 : ∀ v : Magma.tup10R405,
    ¬ @Equation4629 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (23 nodes). -/
def ordS10R405_Law4635 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4635. -/
theorem noS10R405_Law4635 : ∀ v : Magma.tup10R405,
    ¬ @Equation4635 (Fin 10) (Magma.srch10R405 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S10R405.E) (tr := S10R405.tr) (z := S10R405.z)
    (st := S10R405.st) (X := S10R405.X) (envs := Magma.envsRed 10 S10R405.E 2)
    (ord := ordS10R405_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 10) (Magma.srch10R405 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch10R405_refutes_0 :
    FamilyRefutes Magma.srch10R405 [
      3308, 3343, 3511, 3955, 4130, 4158, 4283, 4291, 4629, 4635
    ] :=
  ⟨noS10R405_Law3308, noS10R405_Law3343, noS10R405_Law3511, noS10R405_Law3955, noS10R405_Law4130, noS10R405_Law4158, noS10R405_Law4283, noS10R405_Law4291, noS10R405_Law4629, noS10R405_Law4635⟩

import equational_theories.Definability.Srch_S10R801

/-!
# Structural certificate targets: `Magma.srch10R801`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R801_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 2,622 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R801_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3281 takes them (115 nodes). -/
def ordS10R801_Law3281 : List (Fin 8) := [2, 0, 6, 5, 7, 4, 3, 1]

/-- No member of the class satisfies equation 3281. -/
theorem noS10R801_Law3281 : ∀ v : Magma.tup10R801,
    ¬ @Equation3281 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 2)
    (ord := ordS10R801_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3665 takes them (316 nodes). -/
def ordS10R801_Law3665 : List (Fin 8) := [5, 3, 2, 0, 1, 7, 4, 6]

/-- No member of the class satisfies equation 3665. -/
theorem noS10R801_Law3665 : ∀ v : Magma.tup10R801,
    ¬ @Equation3665 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3665) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 2)
    (ord := ordS10R801_Law3665) (by native_decide) v.1 v.2
    ((@Law3665.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3666 takes them (266 nodes). -/
def ordS10R801_Law3666 : List (Fin 8) := [5, 3, 6, 7, 4, 0, 1, 2]

/-- No member of the class satisfies equation 3666. -/
theorem noS10R801_Law3666 : ∀ v : Magma.tup10R801,
    ¬ @Equation3666 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3666) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law3666) (by native_decide) v.1 v.2
    ((@Law3666.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3677 takes them (265 nodes). -/
def ordS10R801_Law3677 : List (Fin 8) := [5, 7, 0, 1, 6, 2, 3, 4]

/-- No member of the class satisfies equation 3677. -/
theorem noS10R801_Law3677 : ∀ v : Magma.tup10R801,
    ¬ @Equation3677 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3677) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 2)
    (ord := ordS10R801_Law3677) (by native_decide) v.1 v.2
    ((@Law3677.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3680 takes them (151 nodes). -/
def ordS10R801_Law3680 : List (Fin 8) := [7, 5, 4, 2, 0, 1, 3, 6]

/-- No member of the class satisfies equation 3680. -/
theorem noS10R801_Law3680 : ∀ v : Magma.tup10R801,
    ¬ @Equation3680 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3680) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law3680) (by native_decide) v.1 v.2
    ((@Law3680.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (157 nodes). -/
def ordS10R801_Law4074 : List (Fin 8) := [5, 2, 0, 4, 7, 6, 3, 1]

/-- No member of the class satisfies equation 4074. -/
theorem noS10R801_Law4074 : ∀ v : Magma.tup10R801,
    ¬ @Equation4074 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 2)
    (ord := ordS10R801_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (211 nodes). -/
def ordS10R801_Law4362 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4362. -/
theorem noS10R801_Law4362 : ∀ v : Magma.tup10R801,
    ¬ @Equation4362 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (292 nodes). -/
def ordS10R801_Law4401 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4401. -/
theorem noS10R801_Law4401 : ∀ v : Magma.tup10R801,
    ¬ @Equation4401 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4438 takes them (348 nodes). -/
def ordS10R801_Law4438 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4438. -/
theorem noS10R801_Law4438 : ∀ v : Magma.tup10R801,
    ¬ @Equation4438 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4438) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law4438) (by native_decide) v.1 v.2
    ((@Law4438.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4452 takes them (178 nodes). -/
def ordS10R801_Law4452 : List (Fin 8) := [5, 1, 7, 2, 0, 3, 6, 4]

/-- No member of the class satisfies equation 4452. -/
theorem noS10R801_Law4452 : ∀ v : Magma.tup10R801,
    ¬ @Equation4452 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (323 nodes). -/
def ordS10R801_Law4673 : List (Fin 8) := [4, 5, 1, 6, 2, 7, 0, 3]

/-- No member of the class satisfies equation 4673. -/
theorem noS10R801_Law4673 : ∀ v : Magma.tup10R801,
    ¬ @Equation4673 (Fin 10) (Magma.srch10R801 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S10R801.E) (tr := S10R801.tr) (z := S10R801.z)
    (st := S10R801.st) (X := S10R801.X) (envs := Magma.envsRed 10 S10R801.E 3)
    (ord := ordS10R801_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 10) (Magma.srch10R801 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch10R801_refutes_0 :
    FamilyRefutes Magma.srch10R801 [
      3281, 3665, 3666, 3677, 3680, 4074, 4362, 4401, 4438, 4452, 4673
    ] :=
  ⟨noS10R801_Law3281, noS10R801_Law3665, noS10R801_Law3666, noS10R801_Law3677, noS10R801_Law3680, noS10R801_Law4074, noS10R801_Law4362, noS10R801_Law4401, noS10R801_Law4438, noS10R801_Law4452, noS10R801_Law4673⟩

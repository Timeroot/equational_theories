import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 34 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,154 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3316 takes them (1178 nodes). -/
def ordS7R12_Law3316 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3316. -/
theorem noS7R12_Law3316 : ∀ v : Magma.tup7R12,
    ¬ @Equation3316 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3316) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3316) (by native_decide) v.1 v.2
    ((@Law3316.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3317 takes them (110 nodes). -/
def ordS7R12_Law3317 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3317. -/
theorem noS7R12_Law3317 : ∀ v : Magma.tup7R12,
    ¬ @Equation3317 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3317) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3317) (by native_decide) v.1 v.2
    ((@Law3317.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (154 nodes). -/
def ordS7R12_Law3321 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3321. -/
theorem noS7R12_Law3321 : ∀ v : Magma.tup7R12,
    ¬ @Equation3321 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3322 takes them (320 nodes). -/
def ordS7R12_Law3322 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3322. -/
theorem noS7R12_Law3322 : ∀ v : Magma.tup7R12,
    ¬ @Equation3322 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3322) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3322) (by native_decide) v.1 v.2
    ((@Law3322.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (78 nodes). -/
def ordS7R12_Law3324 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3324. -/
theorem noS7R12_Law3324 : ∀ v : Magma.tup7R12,
    ¬ @Equation3324 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (82 nodes). -/
def ordS7R12_Law3326 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3326. -/
theorem noS7R12_Law3326 : ∀ v : Magma.tup7R12,
    ¬ @Equation3326 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (74 nodes). -/
def ordS7R12_Law3331 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3331. -/
theorem noS7R12_Law3331 : ∀ v : Magma.tup7R12,
    ¬ @Equation3331 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (210 nodes). -/
def ordS7R12_Law3334 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3334. -/
theorem noS7R12_Law3334 : ∀ v : Magma.tup7R12,
    ¬ @Equation3334 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3342 takes them (146 nodes). -/
def ordS7R12_Law3342 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3342. -/
theorem noS7R12_Law3342 : ∀ v : Magma.tup7R12,
    ¬ @Equation3342 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3342) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3342) (by native_decide) v.1 v.2
    ((@Law3342.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (277 nodes). -/
def ordS7R12_Law3343 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3343. -/
theorem noS7R12_Law3343 : ∀ v : Magma.tup7R12,
    ¬ @Equation3343 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3346 takes them (467 nodes). -/
def ordS7R12_Law3346 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3346. -/
theorem noS7R12_Law3346 : ∀ v : Magma.tup7R12,
    ¬ @Equation3346 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3346) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3346) (by native_decide) v.1 v.2
    ((@Law3346.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3350 takes them (58 nodes). -/
def ordS7R12_Law3350 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3350. -/
theorem noS7R12_Law3350 : ∀ v : Magma.tup7R12,
    ¬ @Equation3350 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3350) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3350) (by native_decide) v.1 v.2
    ((@Law3350.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch7R12_refutes_33 :
    FamilyRefutes Magma.srch7R12 [
      3316, 3317, 3321, 3322, 3324, 3326, 3331, 3334, 3342, 3343, 3346, 3350
    ] :=
  ⟨noS7R12_Law3316, noS7R12_Law3317, noS7R12_Law3321, noS7R12_Law3322, noS7R12_Law3324, noS7R12_Law3326, noS7R12_Law3331, noS7R12_Law3334, noS7R12_Law3342, noS7R12_Law3343, noS7R12_Law3346, noS7R12_Law3350⟩

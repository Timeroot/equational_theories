import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 1 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `27` equations here, 2,129 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 311 takes them (52 nodes). -/
def ordS7R325_Law311 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 311. -/
theorem noS7R325_Law311 : ∀ v : Magma.tup7R325,
    ¬ @Equation311 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law311) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law311) (by native_decide) v.1 v.2
    ((@Law311.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 314 takes them (10 nodes). -/
def ordS7R325_Law314 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 314. -/
theorem noS7R325_Law314 : ∀ v : Magma.tup7R325,
    ¬ @Equation314 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law314) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law314) (by native_decide) v.1 v.2
    ((@Law314.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 318 takes them (28 nodes). -/
def ordS7R325_Law318 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 318. -/
theorem noS7R325_Law318 : ∀ v : Magma.tup7R325,
    ¬ @Equation318 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law318) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law318) (by native_decide) v.1 v.2
    ((@Law318.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 321 takes them (10 nodes). -/
def ordS7R325_Law321 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 321. -/
theorem noS7R325_Law321 : ∀ v : Magma.tup7R325,
    ¬ @Equation321 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law321) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law321) (by native_decide) v.1 v.2
    ((@Law321.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 343 takes them (18 nodes). -/
def ordS7R325_Law343 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 343. -/
theorem noS7R325_Law343 : ∀ v : Magma.tup7R325,
    ¬ @Equation343 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law343) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law343) (by native_decide) v.1 v.2
    ((@Law343.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 363 takes them (22 nodes). -/
def ordS7R325_Law363 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 363. -/
theorem noS7R325_Law363 : ∀ v : Magma.tup7R325,
    ¬ @Equation363 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law363) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law363) (by native_decide) v.1 v.2
    ((@Law363.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 366 takes them (10 nodes). -/
def ordS7R325_Law366 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 366. -/
theorem noS7R325_Law366 : ∀ v : Magma.tup7R325,
    ¬ @Equation366 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law366) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law366) (by native_decide) v.1 v.2
    ((@Law366.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 370 takes them (58 nodes). -/
def ordS7R325_Law370 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 370. -/
theorem noS7R325_Law370 : ∀ v : Magma.tup7R325,
    ¬ @Equation370 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law370) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law370) (by native_decide) v.1 v.2
    ((@Law370.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 373 takes them (10 nodes). -/
def ordS7R325_Law373 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 373. -/
theorem noS7R325_Law373 : ∀ v : Magma.tup7R325,
    ¬ @Equation373 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law373) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law373) (by native_decide) v.1 v.2
    ((@Law373.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 379 takes them (17 nodes). -/
def ordS7R325_Law379 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 379. -/
theorem noS7R325_Law379 : ∀ v : Magma.tup7R325,
    ¬ @Equation379 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law379) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law379) (by native_decide) v.1 v.2
    ((@Law379.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3267 takes them (52 nodes). -/
def ordS7R325_Law3267 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3267. -/
theorem noS7R325_Law3267 : ∀ v : Magma.tup7R325,
    ¬ @Equation3267 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3267) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3267) (by native_decide) v.1 v.2
    ((@Law3267.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3277 takes them (10 nodes). -/
def ordS7R325_Law3277 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3277. -/
theorem noS7R325_Law3277 : ∀ v : Magma.tup7R325,
    ¬ @Equation3277 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3277) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3277) (by native_decide) v.1 v.2
    ((@Law3277.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3291 takes them (10 nodes). -/
def ordS7R325_Law3291 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3291. -/
theorem noS7R325_Law3291 : ∀ v : Magma.tup7R325,
    ¬ @Equation3291 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3291) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3291) (by native_decide) v.1 v.2
    ((@Law3291.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3300 takes them (46 nodes). -/
def ordS7R325_Law3300 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3300. -/
theorem noS7R325_Law3300 : ∀ v : Magma.tup7R325,
    ¬ @Equation3300 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3300) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3300) (by native_decide) v.1 v.2
    ((@Law3300.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3304 takes them (10 nodes). -/
def ordS7R325_Law3304 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3304. -/
theorem noS7R325_Law3304 : ∀ v : Magma.tup7R325,
    ¬ @Equation3304 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3304) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law3304) (by native_decide) v.1 v.2
    ((@Law3304.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (84 nodes). -/
def ordS7R325_Law3326 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3326. -/
theorem noS7R325_Law3326 : ∀ v : Magma.tup7R325,
    ¬ @Equation3326 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (872 nodes). -/
def ordS7R325_Law3331 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3331. -/
theorem noS7R325_Law3331 : ∀ v : Magma.tup7R325,
    ¬ @Equation3331 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3350 takes them (53 nodes). -/
def ordS7R325_Law3350 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3350. -/
theorem noS7R325_Law3350 : ∀ v : Magma.tup7R325,
    ¬ @Equation3350 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3350) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3350) (by native_decide) v.1 v.2
    ((@Law3350.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3363 takes them (66 nodes). -/
def ordS7R325_Law3363 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3363. -/
theorem noS7R325_Law3363 : ∀ v : Magma.tup7R325,
    ¬ @Equation3363 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3363) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3363) (by native_decide) v.1 v.2
    ((@Law3363.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3380 takes them (245 nodes). -/
def ordS7R325_Law3380 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3380. -/
theorem noS7R325_Law3380 : ∀ v : Magma.tup7R325,
    ¬ @Equation3380 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3380) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3380) (by native_decide) v.1 v.2
    ((@Law3380.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3397 takes them (294 nodes). -/
def ordS7R325_Law3397 : List (Fin 9) := [0, 2, 5, 3, 8, 7, 6, 1, 4]

/-- No member of the class satisfies equation 3397. -/
theorem noS7R325_Law3397 : ∀ v : Magma.tup7R325,
    ¬ @Equation3397 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3397) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3397) (by native_decide) v.1 v.2
    ((@Law3397.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3431 takes them (42 nodes). -/
def ordS7R325_Law3431 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3431. -/
theorem noS7R325_Law3431 : ∀ v : Magma.tup7R325,
    ¬ @Equation3431 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3431) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3431) (by native_decide) v.1 v.2
    ((@Law3431.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3470 takes them (52 nodes). -/
def ordS7R325_Law3470 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3470. -/
theorem noS7R325_Law3470 : ∀ v : Magma.tup7R325,
    ¬ @Equation3470 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3470) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3470) (by native_decide) v.1 v.2
    ((@Law3470.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3480 takes them (10 nodes). -/
def ordS7R325_Law3480 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3480. -/
theorem noS7R325_Law3480 : ∀ v : Magma.tup7R325,
    ¬ @Equation3480 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3480) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3480) (by native_decide) v.1 v.2
    ((@Law3480.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3494 takes them (10 nodes). -/
def ordS7R325_Law3494 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3494. -/
theorem noS7R325_Law3494 : ∀ v : Magma.tup7R325,
    ¬ @Equation3494 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3494) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3494) (by native_decide) v.1 v.2
    ((@Law3494.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3503 takes them (28 nodes). -/
def ordS7R325_Law3503 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3503. -/
theorem noS7R325_Law3503 : ∀ v : Magma.tup7R325,
    ¬ @Equation3503 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3503) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3503) (by native_decide) v.1 v.2
    ((@Law3503.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3507 takes them (10 nodes). -/
def ordS7R325_Law3507 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3507. -/
theorem noS7R325_Law3507 : ∀ v : Magma.tup7R325,
    ¬ @Equation3507 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3507) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law3507) (by native_decide) v.1 v.2
    ((@Law3507.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `27` equations. -/
theorem srch7R325_refutes_0 :
    FamilyRefutes Magma.srch7R325 [
      311, 314, 318, 321, 343, 363, 366, 370, 373, 379, 3267, 3277, 3291, 3300, 3304, 3326, 3331,
      3350, 3363, 3380, 3397, 3431, 3470, 3480, 3494, 3503, 3507
    ] :=
  ⟨noS7R325_Law311, noS7R325_Law314, noS7R325_Law318, noS7R325_Law321, noS7R325_Law343, noS7R325_Law363, noS7R325_Law366, noS7R325_Law370, noS7R325_Law373, noS7R325_Law379, noS7R325_Law3267, noS7R325_Law3277, noS7R325_Law3291, noS7R325_Law3300, noS7R325_Law3304, noS7R325_Law3326, noS7R325_Law3331, noS7R325_Law3350, noS7R325_Law3363, noS7R325_Law3380, noS7R325_Law3397, noS7R325_Law3431, noS7R325_Law3470, noS7R325_Law3480, noS7R325_Law3494, noS7R325_Law3503, noS7R325_Law3507⟩

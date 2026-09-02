import equational_theories.Definability.Srch_S9R400

/-!
# Structural certificate targets: `Magma.srch9R400`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `28` equations here, 1,044 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 310 takes them (19 nodes). -/
def ordS9R400_Law310 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 310. -/
theorem noS9R400_Law310 : ∀ v : Magma.tup9R400,
    ¬ @Equation310 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law310) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law310) (by native_decide) v.1 v.2
    ((@Law310.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 367 takes them (19 nodes). -/
def ordS9R400_Law367 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 367. -/
theorem noS9R400_Law367 : ∀ v : Magma.tup9R400,
    ¬ @Equation367 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law367) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law367) (by native_decide) v.1 v.2
    ((@Law367.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3262 takes them (61 nodes). -/
def ordS9R400_Law3262 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3262. -/
theorem noS9R400_Law3262 : ∀ v : Magma.tup9R400,
    ¬ @Equation3262 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3262) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law3262) (by native_decide) v.1 v.2
    ((@Law3262.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3263 takes them (33 nodes). -/
def ordS9R400_Law3263 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3263. -/
theorem noS9R400_Law3263 : ∀ v : Magma.tup9R400,
    ¬ @Equation3263 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3263) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3263) (by native_decide) v.1 v.2
    ((@Law3263.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3266 takes them (19 nodes). -/
def ordS9R400_Law3266 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3266. -/
theorem noS9R400_Law3266 : ∀ v : Magma.tup9R400,
    ¬ @Equation3266 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3266) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3266) (by native_decide) v.1 v.2
    ((@Law3266.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3323 takes them (49 nodes). -/
def ordS9R400_Law3323 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3323. -/
theorem noS9R400_Law3323 : ∀ v : Magma.tup9R400,
    ¬ @Equation3323 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3323) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3323) (by native_decide) v.1 v.2
    ((@Law3323.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3465 takes them (61 nodes). -/
def ordS9R400_Law3465 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3465. -/
theorem noS9R400_Law3465 : ∀ v : Magma.tup9R400,
    ¬ @Equation3465 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3465) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law3465) (by native_decide) v.1 v.2
    ((@Law3465.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3466 takes them (19 nodes). -/
def ordS9R400_Law3466 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3466. -/
theorem noS9R400_Law3466 : ∀ v : Magma.tup9R400,
    ¬ @Equation3466 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3466) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3466) (by native_decide) v.1 v.2
    ((@Law3466.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3469 takes them (34 nodes). -/
def ordS9R400_Law3469 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3469. -/
theorem noS9R400_Law3469 : ∀ v : Magma.tup9R400,
    ¬ @Equation3469 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3469) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3469) (by native_decide) v.1 v.2
    ((@Law3469.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3890 takes them (61 nodes). -/
def ordS9R400_Law3890 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3890. -/
theorem noS9R400_Law3890 : ∀ v : Magma.tup9R400,
    ¬ @Equation3890 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3890) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law3890) (by native_decide) v.1 v.2
    ((@Law3890.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3893 takes them (34 nodes). -/
def ordS9R400_Law3893 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3893. -/
theorem noS9R400_Law3893 : ∀ v : Magma.tup9R400,
    ¬ @Equation3893 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3893) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3893) (by native_decide) v.1 v.2
    ((@Law3893.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3905 takes them (19 nodes). -/
def ordS9R400_Law3905 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3905. -/
theorem noS9R400_Law3905 : ∀ v : Magma.tup9R400,
    ¬ @Equation3905 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3905) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law3905) (by native_decide) v.1 v.2
    ((@Law3905.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4093 takes them (61 nodes). -/
def ordS9R400_Law4093 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4093. -/
theorem noS9R400_Law4093 : ∀ v : Magma.tup9R400,
    ¬ @Equation4093 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4093) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law4093) (by native_decide) v.1 v.2
    ((@Law4093.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4096 takes them (19 nodes). -/
def ordS9R400_Law4096 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4096. -/
theorem noS9R400_Law4096 : ∀ v : Magma.tup9R400,
    ¬ @Equation4096 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4096) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4096) (by native_decide) v.1 v.2
    ((@Law4096.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4108 takes them (33 nodes). -/
def ordS9R400_Law4108 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4108. -/
theorem noS9R400_Law4108 : ∀ v : Magma.tup9R400,
    ¬ @Equation4108 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4108) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4108) (by native_decide) v.1 v.2
    ((@Law4108.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4226 takes them (49 nodes). -/
def ordS9R400_Law4226 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4226. -/
theorem noS9R400_Law4226 : ∀ v : Magma.tup9R400,
    ¬ @Equation4226 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4226) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4226) (by native_decide) v.1 v.2
    ((@Law4226.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4270 takes them (61 nodes). -/
def ordS9R400_Law4270 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4270. -/
theorem noS9R400_Law4270 : ∀ v : Magma.tup9R400,
    ¬ @Equation4270 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4270) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law4270) (by native_decide) v.1 v.2
    ((@Law4270.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4272 takes them (61 nodes). -/
def ordS9R400_Law4272 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4272. -/
theorem noS9R400_Law4272 : ∀ v : Magma.tup9R400,
    ¬ @Equation4272 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4272) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law4272) (by native_decide) v.1 v.2
    ((@Law4272.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4288 takes them (33 nodes). -/
def ordS9R400_Law4288 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4288. -/
theorem noS9R400_Law4288 : ∀ v : Magma.tup9R400,
    ¬ @Equation4288 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4288) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4288) (by native_decide) v.1 v.2
    ((@Law4288.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4304 takes them (34 nodes). -/
def ordS9R400_Law4304 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4304. -/
theorem noS9R400_Law4304 : ∀ v : Magma.tup9R400,
    ¬ @Equation4304 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4304) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4304) (by native_decide) v.1 v.2
    ((@Law4304.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4341 takes them (19 nodes). -/
def ordS9R400_Law4341 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4341. -/
theorem noS9R400_Law4341 : ∀ v : Magma.tup9R400,
    ¬ @Equation4341 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4341) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4341) (by native_decide) v.1 v.2
    ((@Law4341.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4351 takes them (19 nodes). -/
def ordS9R400_Law4351 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4351. -/
theorem noS9R400_Law4351 : ∀ v : Magma.tup9R400,
    ¬ @Equation4351 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4351) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4351) (by native_decide) v.1 v.2
    ((@Law4351.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4583 takes them (61 nodes). -/
def ordS9R400_Law4583 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4583. -/
theorem noS9R400_Law4583 : ∀ v : Magma.tup9R400,
    ¬ @Equation4583 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4583) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law4583) (by native_decide) v.1 v.2
    ((@Law4583.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4590 takes them (61 nodes). -/
def ordS9R400_Law4590 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4590. -/
theorem noS9R400_Law4590 : ∀ v : Magma.tup9R400,
    ¬ @Equation4590 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4590) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 2)
    (ord := ordS9R400_Law4590) (by native_decide) v.1 v.2
    ((@Law4590.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4597 takes them (19 nodes). -/
def ordS9R400_Law4597 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4597. -/
theorem noS9R400_Law4597 : ∀ v : Magma.tup9R400,
    ¬ @Equation4597 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4597) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4597) (by native_decide) v.1 v.2
    ((@Law4597.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4603 takes them (34 nodes). -/
def ordS9R400_Law4603 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4603. -/
theorem noS9R400_Law4603 : ∀ v : Magma.tup9R400,
    ¬ @Equation4603 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4603) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4603) (by native_decide) v.1 v.2
    ((@Law4603.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4619 takes them (33 nodes). -/
def ordS9R400_Law4619 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4619. -/
theorem noS9R400_Law4619 : ∀ v : Magma.tup9R400,
    ¬ @Equation4619 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4619) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4619) (by native_decide) v.1 v.2
    ((@Law4619.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4622 takes them (19 nodes). -/
def ordS9R400_Law4622 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4622. -/
theorem noS9R400_Law4622 : ∀ v : Magma.tup9R400,
    ¬ @Equation4622 (Fin 9) (Magma.srch9R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4622) (E := S9R400.E) (tr := S9R400.tr) (z := S9R400.z)
    (st := S9R400.st) (X := S9R400.X) (envs := Magma.envsRed 9 S9R400.E 3)
    (ord := ordS9R400_Law4622) (by native_decide) v.1 v.2
    ((@Law4622.models_iff (Fin 9) (Magma.srch9R400 v)).mpr hv)

/-- No member of the class satisfies any of these `28` equations. -/
theorem srch9R400_refutes_0 :
    FamilyRefutes Magma.srch9R400 [
      310, 367, 3262, 3263, 3266, 3323, 3465, 3466, 3469, 3890, 3893, 3905, 4093, 4096, 4108,
      4226, 4270, 4272, 4288, 4304, 4341, 4351, 4583, 4590, 4597, 4603, 4619, 4622
    ] :=
  ⟨noS9R400_Law310, noS9R400_Law367, noS9R400_Law3262, noS9R400_Law3263, noS9R400_Law3266, noS9R400_Law3323, noS9R400_Law3465, noS9R400_Law3466, noS9R400_Law3469, noS9R400_Law3890, noS9R400_Law3893, noS9R400_Law3905, noS9R400_Law4093, noS9R400_Law4096, noS9R400_Law4108, noS9R400_Law4226, noS9R400_Law4270, noS9R400_Law4272, noS9R400_Law4288, noS9R400_Law4304, noS9R400_Law4341, noS9R400_Law4351, noS9R400_Law4583, noS9R400_Law4590, noS9R400_Law4597, noS9R400_Law4603, noS9R400_Law4619, noS9R400_Law4622⟩

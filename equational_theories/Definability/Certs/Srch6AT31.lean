import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 32 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `19`
equations here, 3,192 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3345 takes them (607 nodes). -/
def ordS6A_Law3345 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3345. -/
theorem noS6A_Law3345 : ∀ v : Magma.tupS6A,
    ¬ @Equation3345 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3345) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3345) (by native_decide) v.1 v.2
    ((@Law3345.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3347 takes them (37 nodes). -/
def ordS6A_Law3347 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3347. -/
theorem noS6A_Law3347 : ∀ v : Magma.tupS6A,
    ¬ @Equation3347 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3347) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3347) (by native_decide) v.1 v.2
    ((@Law3347.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3348 takes them (118 nodes). -/
def ordS6A_Law3348 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3348. -/
theorem noS6A_Law3348 : ∀ v : Magma.tupS6A,
    ¬ @Equation3348 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3348) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3348) (by native_decide) v.1 v.2
    ((@Law3348.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3349 takes them (160 nodes). -/
def ordS6A_Law3349 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3349. -/
theorem noS6A_Law3349 : ∀ v : Magma.tupS6A,
    ¬ @Equation3349 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3349) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3349) (by native_decide) v.1 v.2
    ((@Law3349.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3351 takes them (31 nodes). -/
def ordS6A_Law3351 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3351. -/
theorem noS6A_Law3351 : ∀ v : Magma.tupS6A,
    ¬ @Equation3351 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3351) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3351) (by native_decide) v.1 v.2
    ((@Law3351.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3352 takes them (287 nodes). -/
def ordS6A_Law3352 : List (Fin 11) := [9, 0, 5, 2, 10, 4, 1, 8, 3, 6, 7]

/-- No member of the class satisfies equation 3352. -/
theorem noS6A_Law3352 : ∀ v : Magma.tupS6A,
    ¬ @Equation3352 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3352) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3352) (by native_decide) v.1 v.2
    ((@Law3352.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3354 takes them (31 nodes). -/
def ordS6A_Law3354 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3354. -/
theorem noS6A_Law3354 : ∀ v : Magma.tupS6A,
    ¬ @Equation3354 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3354) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3354) (by native_decide) v.1 v.2
    ((@Law3354.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3355 takes them (701 nodes). -/
def ordS6A_Law3355 : List (Fin 11) := [1, 0, 8, 9, 4, 6, 5, 10, 2, 3, 7]

/-- No member of the class satisfies equation 3355. -/
theorem noS6A_Law3355 : ∀ v : Magma.tupS6A,
    ¬ @Equation3355 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3355) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3355) (by native_decide) v.1 v.2
    ((@Law3355.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3356 takes them (225 nodes). -/
def ordS6A_Law3356 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3356. -/
theorem noS6A_Law3356 : ∀ v : Magma.tupS6A,
    ¬ @Equation3356 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3356) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3356) (by native_decide) v.1 v.2
    ((@Law3356.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3357 takes them (29 nodes). -/
def ordS6A_Law3357 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3357. -/
theorem noS6A_Law3357 : ∀ v : Magma.tupS6A,
    ¬ @Equation3357 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3357) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3357) (by native_decide) v.1 v.2
    ((@Law3357.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3358 takes them (70 nodes). -/
def ordS6A_Law3358 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3358. -/
theorem noS6A_Law3358 : ∀ v : Magma.tupS6A,
    ¬ @Equation3358 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3358) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3358) (by native_decide) v.1 v.2
    ((@Law3358.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3359 takes them (156 nodes). -/
def ordS6A_Law3359 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3359. -/
theorem noS6A_Law3359 : ∀ v : Magma.tupS6A,
    ¬ @Equation3359 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3359) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3359) (by native_decide) v.1 v.2
    ((@Law3359.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3360 takes them (78 nodes). -/
def ordS6A_Law3360 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3360. -/
theorem noS6A_Law3360 : ∀ v : Magma.tupS6A,
    ¬ @Equation3360 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3360) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3360) (by native_decide) v.1 v.2
    ((@Law3360.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3361 takes them (29 nodes). -/
def ordS6A_Law3361 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3361. -/
theorem noS6A_Law3361 : ∀ v : Magma.tupS6A,
    ¬ @Equation3361 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3361) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3361) (by native_decide) v.1 v.2
    ((@Law3361.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3362 takes them (173 nodes). -/
def ordS6A_Law3362 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3362. -/
theorem noS6A_Law3362 : ∀ v : Magma.tupS6A,
    ¬ @Equation3362 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3362) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3362) (by native_decide) v.1 v.2
    ((@Law3362.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3364 takes them (166 nodes). -/
def ordS6A_Law3364 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3364. -/
theorem noS6A_Law3364 : ∀ v : Magma.tupS6A,
    ¬ @Equation3364 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3364) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3364) (by native_decide) v.1 v.2
    ((@Law3364.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3365 takes them (29 nodes). -/
def ordS6A_Law3365 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3365. -/
theorem noS6A_Law3365 : ∀ v : Magma.tupS6A,
    ¬ @Equation3365 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3365) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3365) (by native_decide) v.1 v.2
    ((@Law3365.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3366 takes them (74 nodes). -/
def ordS6A_Law3366 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3366. -/
theorem noS6A_Law3366 : ∀ v : Magma.tupS6A,
    ¬ @Equation3366 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3366) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3366) (by native_decide) v.1 v.2
    ((@Law3366.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3367 takes them (191 nodes). -/
def ordS6A_Law3367 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3367. -/
theorem noS6A_Law3367 : ∀ v : Magma.tupS6A,
    ¬ @Equation3367 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3367) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3367) (by native_decide) v.1 v.2
    ((@Law3367.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srch6A_refutes_31 :
    FamilyRefutes Magma.srch6A [
      3345, 3347, 3348, 3349, 3351, 3352, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362,
      3364, 3365, 3366, 3367
    ] :=
  ⟨noS6A_Law3345, noS6A_Law3347, noS6A_Law3348, noS6A_Law3349, noS6A_Law3351, noS6A_Law3352, noS6A_Law3354, noS6A_Law3355, noS6A_Law3356, noS6A_Law3357, noS6A_Law3358, noS6A_Law3359, noS6A_Law3360, noS6A_Law3361, noS6A_Law3362, noS6A_Law3364, noS6A_Law3365, noS6A_Law3366, noS6A_Law3367⟩

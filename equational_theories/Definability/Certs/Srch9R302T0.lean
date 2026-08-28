import equational_theories.Definability.Srch_S9R302

/-!
# Structural certificate targets: `Magma.srch9R302` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R302_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `41` equations here, 2,333 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R302_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 473 takes them (65 nodes). -/
def ordS9R302_Law473 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 473. -/
theorem noS9R302_Law473 : ∀ v : Magma.tup9R302,
    ¬ @Equation473 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (37 nodes). -/
def ordS9R302_Law562 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 562. -/
theorem noS9R302_Law562 : ∀ v : Magma.tup9R302,
    ¬ @Equation562 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 879 takes them (68 nodes). -/
def ordS9R302_Law879 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 879. -/
theorem noS9R302_Law879 : ∀ v : Magma.tup9R302,
    ¬ @Equation879 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law879) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law879) (by native_decide) v.1 v.2
    ((@Law879.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1340 takes them (38 nodes). -/
def ordS9R302_Law1340 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1340. -/
theorem noS9R302_Law1340 : ∀ v : Magma.tup9R302,
    ¬ @Equation1340 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1340) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law1340) (by native_decide) v.1 v.2
    ((@Law1340.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (54 nodes). -/
def ordS9R302_Law1374 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1374. -/
theorem noS9R302_Law1374 : ∀ v : Magma.tup9R302,
    ¬ @Equation1374 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (42 nodes). -/
def ordS9R302_Law1467 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1467. -/
theorem noS9R302_Law1467 : ∀ v : Magma.tup9R302,
    ¬ @Equation1467 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1470 takes them (39 nodes). -/
def ordS9R302_Law1470 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1470. -/
theorem noS9R302_Law1470 : ∀ v : Magma.tup9R302,
    ¬ @Equation1470 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1470) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law1470) (by native_decide) v.1 v.2
    ((@Law1470.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (57 nodes). -/
def ordS9R302_Law2186 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2186. -/
theorem noS9R302_Law2186 : ∀ v : Magma.tup9R302,
    ¬ @Equation2186 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (39 nodes). -/
def ordS9R302_Law2199 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2199. -/
theorem noS9R302_Law2199 : ∀ v : Magma.tup9R302,
    ¬ @Equation2199 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2271 takes them (50 nodes). -/
def ordS9R302_Law2271 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2271. -/
theorem noS9R302_Law2271 : ∀ v : Magma.tup9R302,
    ¬ @Equation2271 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2271) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law2271) (by native_decide) v.1 v.2
    ((@Law2271.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (52 nodes). -/
def ordS9R302_Law2279 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2279. -/
theorem noS9R302_Law2279 : ∀ v : Magma.tup9R302,
    ¬ @Equation2279 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2650 takes them (138 nodes). -/
def ordS9R302_Law2650 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2650. -/
theorem noS9R302_Law2650 : ∀ v : Magma.tup9R302,
    ¬ @Equation2650 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2650) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law2650) (by native_decide) v.1 v.2
    ((@Law2650.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (185 nodes). -/
def ordS9R302_Law3056 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3056. -/
theorem noS9R302_Law3056 : ∀ v : Magma.tup9R302,
    ¬ @Equation3056 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (91 nodes). -/
def ordS9R302_Law3091 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3091. -/
theorem noS9R302_Law3091 : ∀ v : Magma.tup9R302,
    ¬ @Equation3091 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3279 takes them (123 nodes). -/
def ordS9R302_Law3279 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3279. -/
theorem noS9R302_Law3279 : ∀ v : Magma.tup9R302,
    ¬ @Equation3279 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3279) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3279) (by native_decide) v.1 v.2
    ((@Law3279.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (42 nodes). -/
def ordS9R302_Law3331 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3331. -/
theorem noS9R302_Law3331 : ∀ v : Magma.tup9R302,
    ¬ @Equation3331 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3364 takes them (20 nodes). -/
def ordS9R302_Law3364 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3364. -/
theorem noS9R302_Law3364 : ∀ v : Magma.tup9R302,
    ¬ @Equation3364 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3364) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3364) (by native_decide) v.1 v.2
    ((@Law3364.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3370 takes them (20 nodes). -/
def ordS9R302_Law3370 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3370. -/
theorem noS9R302_Law3370 : ∀ v : Magma.tup9R302,
    ¬ @Equation3370 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3370) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3370) (by native_decide) v.1 v.2
    ((@Law3370.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3388 takes them (41 nodes). -/
def ordS9R302_Law3388 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3388. -/
theorem noS9R302_Law3388 : ∀ v : Magma.tup9R302,
    ¬ @Equation3388 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3388) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3388) (by native_decide) v.1 v.2
    ((@Law3388.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3417 takes them (18 nodes). -/
def ordS9R302_Law3417 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3417. -/
theorem noS9R302_Law3417 : ∀ v : Magma.tup9R302,
    ¬ @Equation3417 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3417) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3417) (by native_decide) v.1 v.2
    ((@Law3417.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3475 takes them (62 nodes). -/
def ordS9R302_Law3475 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3475. -/
theorem noS9R302_Law3475 : ∀ v : Magma.tup9R302,
    ¬ @Equation3475 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3475) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3475) (by native_decide) v.1 v.2
    ((@Law3475.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3482 takes them (110 nodes). -/
def ordS9R302_Law3482 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3482. -/
theorem noS9R302_Law3482 : ∀ v : Magma.tup9R302,
    ¬ @Equation3482 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3482) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3482) (by native_decide) v.1 v.2
    ((@Law3482.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (45 nodes). -/
def ordS9R302_Law3534 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3534. -/
theorem noS9R302_Law3534 : ∀ v : Magma.tup9R302,
    ¬ @Equation3534 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3553 takes them (30 nodes). -/
def ordS9R302_Law3553 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3553. -/
theorem noS9R302_Law3553 : ∀ v : Magma.tup9R302,
    ¬ @Equation3553 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3553) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3553) (by native_decide) v.1 v.2
    ((@Law3553.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3567 takes them (30 nodes). -/
def ordS9R302_Law3567 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3567. -/
theorem noS9R302_Law3567 : ∀ v : Magma.tup9R302,
    ¬ @Equation3567 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3567) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3567) (by native_decide) v.1 v.2
    ((@Law3567.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3588 takes them (14 nodes). -/
def ordS9R302_Law3588 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3588. -/
theorem noS9R302_Law3588 : ∀ v : Magma.tup9R302,
    ¬ @Equation3588 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3588) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3588) (by native_decide) v.1 v.2
    ((@Law3588.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3607 takes them (19 nodes). -/
def ordS9R302_Law3607 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3607. -/
theorem noS9R302_Law3607 : ∀ v : Magma.tup9R302,
    ¬ @Equation3607 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3607) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3607) (by native_decide) v.1 v.2
    ((@Law3607.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3881 takes them (111 nodes). -/
def ordS9R302_Law3881 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3881. -/
theorem noS9R302_Law3881 : ∀ v : Magma.tup9R302,
    ¬ @Equation3881 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3881) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3881) (by native_decide) v.1 v.2
    ((@Law3881.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3888 takes them (66 nodes). -/
def ordS9R302_Law3888 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3888. -/
theorem noS9R302_Law3888 : ∀ v : Magma.tup9R302,
    ¬ @Equation3888 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3888) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law3888) (by native_decide) v.1 v.2
    ((@Law3888.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3973 takes them (19 nodes). -/
def ordS9R302_Law3973 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3973. -/
theorem noS9R302_Law3973 : ∀ v : Magma.tup9R302,
    ¬ @Equation3973 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3973) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3973) (by native_decide) v.1 v.2
    ((@Law3973.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3994 takes them (25 nodes). -/
def ordS9R302_Law3994 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3994. -/
theorem noS9R302_Law3994 : ∀ v : Magma.tup9R302,
    ¬ @Equation3994 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3994) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3994) (by native_decide) v.1 v.2
    ((@Law3994.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (52 nodes). -/
def ordS9R302_Law3997 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3997. -/
theorem noS9R302_Law3997 : ∀ v : Magma.tup9R302,
    ¬ @Equation3997 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4013 takes them (35 nodes). -/
def ordS9R302_Law4013 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4013. -/
theorem noS9R302_Law4013 : ∀ v : Magma.tup9R302,
    ¬ @Equation4013 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4013) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4013) (by native_decide) v.1 v.2
    ((@Law4013.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4026 takes them (35 nodes). -/
def ordS9R302_Law4026 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4026. -/
theorem noS9R302_Law4026 : ∀ v : Magma.tup9R302,
    ¬ @Equation4026 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4026) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4026) (by native_decide) v.1 v.2
    ((@Law4026.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4084 takes them (162 nodes). -/
def ordS9R302_Law4084 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4084. -/
theorem noS9R302_Law4084 : ∀ v : Magma.tup9R302,
    ¬ @Equation4084 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4084) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law4084) (by native_decide) v.1 v.2
    ((@Law4084.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4143 takes them (81 nodes). -/
def ordS9R302_Law4143 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4143. -/
theorem noS9R302_Law4143 : ∀ v : Magma.tup9R302,
    ¬ @Equation4143 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4162 takes them (28 nodes). -/
def ordS9R302_Law4162 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4162. -/
theorem noS9R302_Law4162 : ∀ v : Magma.tup9R302,
    ¬ @Equation4162 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4162) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4162) (by native_decide) v.1 v.2
    ((@Law4162.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4182 takes them (45 nodes). -/
def ordS9R302_Law4182 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4182. -/
theorem noS9R302_Law4182 : ∀ v : Magma.tup9R302,
    ¬ @Equation4182 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4182) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4182) (by native_decide) v.1 v.2
    ((@Law4182.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (79 nodes). -/
def ordS9R302_Law4200 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4200. -/
theorem noS9R302_Law4200 : ∀ v : Magma.tup9R302,
    ¬ @Equation4200 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4216 takes them (47 nodes). -/
def ordS9R302_Law4216 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4216. -/
theorem noS9R302_Law4216 : ∀ v : Magma.tup9R302,
    ¬ @Equation4216 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4216) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4216) (by native_decide) v.1 v.2
    ((@Law4216.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4305 takes them (19 nodes). -/
def ordS9R302_Law4305 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4305. -/
theorem noS9R302_Law4305 : ∀ v : Magma.tup9R302,
    ¬ @Equation4305 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4305) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4305) (by native_decide) v.1 v.2
    ((@Law4305.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- No member of the class satisfies any of these `41` equations. -/
theorem srch9R302_refutes_0 :
    FamilyRefutes Magma.srch9R302 [
      473, 562, 879, 1340, 1374, 1467, 1470, 2186, 2199, 2271, 2279, 2650, 3056, 3091, 3279,
      3331, 3364, 3370, 3388, 3417, 3475, 3482, 3534, 3553, 3567, 3588, 3607, 3881, 3888, 3973,
      3994, 3997, 4013, 4026, 4084, 4143, 4162, 4182, 4200, 4216, 4305
    ] :=
  ⟨noS9R302_Law473, noS9R302_Law562, noS9R302_Law879, noS9R302_Law1340, noS9R302_Law1374, noS9R302_Law1467, noS9R302_Law1470, noS9R302_Law2186, noS9R302_Law2199, noS9R302_Law2271, noS9R302_Law2279, noS9R302_Law2650, noS9R302_Law3056, noS9R302_Law3091, noS9R302_Law3279, noS9R302_Law3331, noS9R302_Law3364, noS9R302_Law3370, noS9R302_Law3388, noS9R302_Law3417, noS9R302_Law3475, noS9R302_Law3482, noS9R302_Law3534, noS9R302_Law3553, noS9R302_Law3567, noS9R302_Law3588, noS9R302_Law3607, noS9R302_Law3881, noS9R302_Law3888, noS9R302_Law3973, noS9R302_Law3994, noS9R302_Law3997, noS9R302_Law4013, noS9R302_Law4026, noS9R302_Law4084, noS9R302_Law4143, noS9R302_Law4162, noS9R302_Law4182, noS9R302_Law4200, noS9R302_Law4216, noS9R302_Law4305⟩

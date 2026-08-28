import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 5 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `20`
equations here, 3,058 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3263 takes them (118 nodes). -/
def ordSR25_Law3263 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3263. -/
theorem noSR25_Law3263 : ∀ v : Magma.tupR25,
    ¬ @Equation3263 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3263) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3263) (by native_decide) v.1 v.2
    ((@Law3263.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (119 nodes). -/
def ordSR25_Law3265 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3265. -/
theorem noSR25_Law3265 : ∀ v : Magma.tupR25,
    ¬ @Equation3265 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3266 takes them (118 nodes). -/
def ordSR25_Law3266 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3266. -/
theorem noSR25_Law3266 : ∀ v : Magma.tupR25,
    ¬ @Equation3266 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3266) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3266) (by native_decide) v.1 v.2
    ((@Law3266.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (225 nodes). -/
def ordSR25_Law3278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3278. -/
theorem noSR25_Law3278 : ∀ v : Magma.tupR25,
    ¬ @Equation3278 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (214 nodes). -/
def ordSR25_Law3334 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3334. -/
theorem noSR25_Law3334 : ∀ v : Magma.tupR25,
    ¬ @Equation3334 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (149 nodes). -/
def ordSR25_Law3414 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3414. -/
theorem noSR25_Law3414 : ∀ v : Magma.tupR25,
    ¬ @Equation3414 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3463 takes them (86 nodes). -/
def ordSR25_Law3463 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3463. -/
theorem noSR25_Law3463 : ∀ v : Magma.tupR25,
    ¬ @Equation3463 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3463) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3463) (by native_decide) v.1 v.2
    ((@Law3463.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3465 takes them (246 nodes). -/
def ordSR25_Law3465 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3465. -/
theorem noSR25_Law3465 : ∀ v : Magma.tupR25,
    ¬ @Equation3465 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3465) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3465) (by native_decide) v.1 v.2
    ((@Law3465.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3466 takes them (100 nodes). -/
def ordSR25_Law3466 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3466. -/
theorem noSR25_Law3466 : ∀ v : Magma.tupR25,
    ¬ @Equation3466 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3466) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3466) (by native_decide) v.1 v.2
    ((@Law3466.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3468 takes them (127 nodes). -/
def ordSR25_Law3468 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3468. -/
theorem noSR25_Law3468 : ∀ v : Magma.tupR25,
    ¬ @Equation3468 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3469 takes them (119 nodes). -/
def ordSR25_Law3469 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3469. -/
theorem noSR25_Law3469 : ∀ v : Magma.tupR25,
    ¬ @Equation3469 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3469) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3469) (by native_decide) v.1 v.2
    ((@Law3469.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (273 nodes). -/
def ordSR25_Law3484 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3484. -/
theorem noSR25_Law3484 : ∀ v : Magma.tupR25,
    ¬ @Equation3484 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (122 nodes). -/
def ordSR25_Law3529 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3529. -/
theorem noSR25_Law3529 : ∀ v : Magma.tupR25,
    ¬ @Equation3529 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3537 takes them (73 nodes). -/
def ordSR25_Law3537 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3537. -/
theorem noSR25_Law3537 : ∀ v : Magma.tupR25,
    ¬ @Equation3537 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3537) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3537) (by native_decide) v.1 v.2
    ((@Law3537.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (273 nodes). -/
def ordSR25_Law3871 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3871. -/
theorem noSR25_Law3871 : ∀ v : Magma.tupR25,
    ¬ @Equation3871 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3883 takes them (95 nodes). -/
def ordSR25_Law3883 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3883. -/
theorem noSR25_Law3883 : ∀ v : Magma.tupR25,
    ¬ @Equation3883 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3883) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3883) (by native_decide) v.1 v.2
    ((@Law3883.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3890 takes them (246 nodes). -/
def ordSR25_Law3890 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3890. -/
theorem noSR25_Law3890 : ∀ v : Magma.tupR25,
    ¬ @Equation3890 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3890) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3890) (by native_decide) v.1 v.2
    ((@Law3890.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3893 takes them (119 nodes). -/
def ordSR25_Law3893 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3893. -/
theorem noSR25_Law3893 : ∀ v : Magma.tupR25,
    ¬ @Equation3893 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3893) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3893) (by native_decide) v.1 v.2
    ((@Law3893.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3901 takes them (127 nodes). -/
def ordSR25_Law3901 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3901. -/
theorem noSR25_Law3901 : ∀ v : Magma.tupR25,
    ¬ @Equation3901 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3901) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3901) (by native_decide) v.1 v.2
    ((@Law3901.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3905 takes them (109 nodes). -/
def ordSR25_Law3905 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3905. -/
theorem noSR25_Law3905 : ∀ v : Magma.tupR25,
    ¬ @Equation3905 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3905) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3905) (by native_decide) v.1 v.2
    ((@Law3905.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srchR25_refutes_4 :
    FamilyRefutes Magma.srchR25 [
      3263, 3265, 3266, 3278, 3334, 3414, 3463, 3465, 3466, 3468, 3469, 3484, 3529, 3537, 3871,
      3883, 3890, 3893, 3901, 3905
    ] :=
  ⟨noSR25_Law3263, noSR25_Law3265, noSR25_Law3266, noSR25_Law3278, noSR25_Law3334, noSR25_Law3414, noSR25_Law3463, noSR25_Law3465, noSR25_Law3466, noSR25_Law3468, noSR25_Law3469, noSR25_Law3484, noSR25_Law3529, noSR25_Law3537, noSR25_Law3871, noSR25_Law3883, noSR25_Law3890, noSR25_Law3893, noSR25_Law3901, noSR25_Law3905⟩

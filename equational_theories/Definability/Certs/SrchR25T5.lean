import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 6 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `19`
equations here, 3,233 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3931 takes them (136 nodes). -/
def ordSR25_Law3931 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3931. -/
theorem noSR25_Law3931 : ∀ v : Magma.tupR25,
    ¬ @Equation3931 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3943 takes them (81 nodes). -/
def ordSR25_Law3943 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3943. -/
theorem noSR25_Law3943 : ∀ v : Magma.tupR25,
    ¬ @Equation3943 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3943) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3943) (by native_decide) v.1 v.2
    ((@Law3943.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (217 nodes). -/
def ordSR25_Law4068 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4068. -/
theorem noSR25_Law4068 : ∀ v : Magma.tupR25,
    ¬ @Equation4068 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4093 takes them (246 nodes). -/
def ordSR25_Law4093 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4093. -/
theorem noSR25_Law4093 : ∀ v : Magma.tupR25,
    ¬ @Equation4093 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4093) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4093) (by native_decide) v.1 v.2
    ((@Law4093.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4096 takes them (118 nodes). -/
def ordSR25_Law4096 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4096. -/
theorem noSR25_Law4096 : ∀ v : Magma.tupR25,
    ¬ @Equation4096 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4096) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4096) (by native_decide) v.1 v.2
    ((@Law4096.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (119 nodes). -/
def ordSR25_Law4104 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4104. -/
theorem noSR25_Law4104 : ∀ v : Magma.tupR25,
    ¬ @Equation4104 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4108 takes them (127 nodes). -/
def ordSR25_Law4108 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4108. -/
theorem noSR25_Law4108 : ∀ v : Magma.tupR25,
    ¬ @Equation4108 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4108) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4108) (by native_decide) v.1 v.2
    ((@Law4108.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (149 nodes). -/
def ordSR25_Law4135 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4135. -/
theorem noSR25_Law4135 : ∀ v : Magma.tupR25,
    ¬ @Equation4135 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (229 nodes). -/
def ordSR25_Law4146 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4146. -/
theorem noSR25_Law4146 : ∀ v : Magma.tupR25,
    ¬ @Equation4146 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4270 takes them (246 nodes). -/
def ordSR25_Law4270 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4270. -/
theorem noSR25_Law4270 : ∀ v : Magma.tupR25,
    ¬ @Equation4270 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4270) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4270) (by native_decide) v.1 v.2
    ((@Law4270.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4272 takes them (156 nodes). -/
def ordSR25_Law4272 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4272. -/
theorem noSR25_Law4272 : ∀ v : Magma.tupR25,
    ¬ @Equation4272 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4272) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4272) (by native_decide) v.1 v.2
    ((@Law4272.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4288 takes them (79 nodes). -/
def ordSR25_Law4288 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4288. -/
theorem noSR25_Law4288 : ∀ v : Magma.tupR25,
    ¬ @Equation4288 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4288) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4288) (by native_decide) v.1 v.2
    ((@Law4288.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4304 takes them (74 nodes). -/
def ordSR25_Law4304 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4304. -/
theorem noSR25_Law4304 : ∀ v : Magma.tupR25,
    ¬ @Equation4304 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4304) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4304) (by native_decide) v.1 v.2
    ((@Law4304.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4318 takes them (92 nodes). -/
def ordSR25_Law4318 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4318. -/
theorem noSR25_Law4318 : ∀ v : Magma.tupR25,
    ¬ @Equation4318 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4318) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4318) (by native_decide) v.1 v.2
    ((@Law4318.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4327 takes them (79 nodes). -/
def ordSR25_Law4327 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4327. -/
theorem noSR25_Law4327 : ∀ v : Magma.tupR25,
    ¬ @Equation4327 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4327) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4327) (by native_decide) v.1 v.2
    ((@Law4327.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4341 takes them (109 nodes). -/
def ordSR25_Law4341 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4341. -/
theorem noSR25_Law4341 : ∀ v : Magma.tupR25,
    ¬ @Equation4341 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4341) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4341) (by native_decide) v.1 v.2
    ((@Law4341.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4351 takes them (73 nodes). -/
def ordSR25_Law4351 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4351. -/
theorem noSR25_Law4351 : ∀ v : Magma.tupR25,
    ¬ @Equation4351 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4351) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4351) (by native_decide) v.1 v.2
    ((@Law4351.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (468 nodes). -/
def ordSR25_Law4383 : List (Fin 8) := [1, 4, 6, 5, 0, 2, 7, 3]

/-- No member of the class satisfies equation 4383. -/
theorem noSR25_Law4383 : ∀ v : Magma.tupR25,
    ¬ @Equation4383 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4409 takes them (435 nodes). -/
def ordSR25_Law4409 : List (Fin 8) := [3, 0, 2, 5, 6, 7, 1, 4]

/-- No member of the class satisfies equation 4409. -/
theorem noSR25_Law4409 : ∀ v : Magma.tupR25,
    ¬ @Equation4409 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srchR25_refutes_5 :
    FamilyRefutes Magma.srchR25 [
      3931, 3943, 4068, 4093, 4096, 4104, 4108, 4135, 4146, 4270, 4272, 4288, 4304, 4318, 4327,
      4341, 4351, 4383, 4409
    ] :=
  ⟨noSR25_Law3931, noSR25_Law3943, noSR25_Law4068, noSR25_Law4093, noSR25_Law4096, noSR25_Law4104, noSR25_Law4108, noSR25_Law4135, noSR25_Law4146, noSR25_Law4270, noSR25_Law4272, noSR25_Law4288, noSR25_Law4304, noSR25_Law4318, noSR25_Law4327, noSR25_Law4341, noSR25_Law4351, noSR25_Law4383, noSR25_Law4409⟩

import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 48 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 3,207 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4310 takes them (22 nodes). -/
def ordS7R12_Law4310 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4310. -/
theorem noS7R12_Law4310 : ∀ v : Magma.tup7R12,
    ¬ @Equation4310 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4311 takes them (36 nodes). -/
def ordS7R12_Law4311 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4311. -/
theorem noS7R12_Law4311 : ∀ v : Magma.tup7R12,
    ¬ @Equation4311 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4311) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4311) (by native_decide) v.1 v.2
    ((@Law4311.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (656 nodes). -/
def ordS7R12_Law4314 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4314. -/
theorem noS7R12_Law4314 : ∀ v : Magma.tup7R12,
    ¬ @Equation4314 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (86 nodes). -/
def ordS7R12_Law4315 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4315. -/
theorem noS7R12_Law4315 : ∀ v : Magma.tup7R12,
    ¬ @Equation4315 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4316 takes them (484 nodes). -/
def ordS7R12_Law4316 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4316. -/
theorem noS7R12_Law4316 : ∀ v : Magma.tup7R12,
    ¬ @Equation4316 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4316) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4316) (by native_decide) v.1 v.2
    ((@Law4316.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4317 takes them (72 nodes). -/
def ordS7R12_Law4317 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4317. -/
theorem noS7R12_Law4317 : ∀ v : Magma.tup7R12,
    ¬ @Equation4317 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4317) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4317) (by native_decide) v.1 v.2
    ((@Law4317.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4318 takes them (222 nodes). -/
def ordS7R12_Law4318 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4318. -/
theorem noS7R12_Law4318 : ∀ v : Magma.tup7R12,
    ¬ @Equation4318 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4318) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4318) (by native_decide) v.1 v.2
    ((@Law4318.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4319 takes them (30 nodes). -/
def ordS7R12_Law4319 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4319. -/
theorem noS7R12_Law4319 : ∀ v : Magma.tup7R12,
    ¬ @Equation4319 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4319) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4319) (by native_decide) v.1 v.2
    ((@Law4319.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4320 takes them (570 nodes). -/
def ordS7R12_Law4320 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4320. -/
theorem noS7R12_Law4320 : ∀ v : Magma.tup7R12,
    ¬ @Equation4320 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4320) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4320) (by native_decide) v.1 v.2
    ((@Law4320.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4323 takes them (50 nodes). -/
def ordS7R12_Law4323 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4323. -/
theorem noS7R12_Law4323 : ∀ v : Magma.tup7R12,
    ¬ @Equation4323 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4324 takes them (195 nodes). -/
def ordS7R12_Law4324 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4324. -/
theorem noS7R12_Law4324 : ∀ v : Magma.tup7R12,
    ¬ @Equation4324 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4324) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4324) (by native_decide) v.1 v.2
    ((@Law4324.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4325 takes them (160 nodes). -/
def ordS7R12_Law4325 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4325. -/
theorem noS7R12_Law4325 : ∀ v : Magma.tup7R12,
    ¬ @Equation4325 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4325) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4325) (by native_decide) v.1 v.2
    ((@Law4325.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4327 takes them (177 nodes). -/
def ordS7R12_Law4327 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4327. -/
theorem noS7R12_Law4327 : ∀ v : Magma.tup7R12,
    ¬ @Equation4327 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4327) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4327) (by native_decide) v.1 v.2
    ((@Law4327.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4330 takes them (40 nodes). -/
def ordS7R12_Law4330 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4330. -/
theorem noS7R12_Law4330 : ∀ v : Magma.tup7R12,
    ¬ @Equation4330 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4330) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4330) (by native_decide) v.1 v.2
    ((@Law4330.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4331 takes them (157 nodes). -/
def ordS7R12_Law4331 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4331. -/
theorem noS7R12_Law4331 : ∀ v : Magma.tup7R12,
    ¬ @Equation4331 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4331) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4331) (by native_decide) v.1 v.2
    ((@Law4331.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4332 takes them (216 nodes). -/
def ordS7R12_Law4332 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4332. -/
theorem noS7R12_Law4332 : ∀ v : Magma.tup7R12,
    ¬ @Equation4332 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4332) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4332) (by native_decide) v.1 v.2
    ((@Law4332.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4334 takes them (34 nodes). -/
def ordS7R12_Law4334 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4334. -/
theorem noS7R12_Law4334 : ∀ v : Magma.tup7R12,
    ¬ @Equation4334 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4334) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4334) (by native_decide) v.1 v.2
    ((@Law4334.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch7R12_refutes_47 :
    FamilyRefutes Magma.srch7R12 [
      4310, 4311, 4314, 4315, 4316, 4317, 4318, 4319, 4320, 4323, 4324, 4325, 4327, 4330, 4331,
      4332, 4334
    ] :=
  ⟨noS7R12_Law4310, noS7R12_Law4311, noS7R12_Law4314, noS7R12_Law4315, noS7R12_Law4316, noS7R12_Law4317, noS7R12_Law4318, noS7R12_Law4319, noS7R12_Law4320, noS7R12_Law4323, noS7R12_Law4324, noS7R12_Law4325, noS7R12_Law4327, noS7R12_Law4330, noS7R12_Law4331, noS7R12_Law4332, noS7R12_Law4334⟩

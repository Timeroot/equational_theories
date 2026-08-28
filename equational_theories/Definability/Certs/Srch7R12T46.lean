import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 47 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `18` equations here, 3,229 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4209 takes them (188 nodes). -/
def ordS7R12_Law4209 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4209. -/
theorem noS7R12_Law4209 : ∀ v : Magma.tup7R12,
    ¬ @Equation4209 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4209) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4209) (by native_decide) v.1 v.2
    ((@Law4209.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4229 takes them (546 nodes). -/
def ordS7R12_Law4229 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4229. -/
theorem noS7R12_Law4229 : ∀ v : Magma.tup7R12,
    ¬ @Equation4229 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4229) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4229) (by native_decide) v.1 v.2
    ((@Law4229.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (156 nodes). -/
def ordS7R12_Law4243 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4243. -/
theorem noS7R12_Law4243 : ∀ v : Magma.tup7R12,
    ¬ @Equation4243 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4269 takes them (568 nodes). -/
def ordS7R12_Law4269 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4269. -/
theorem noS7R12_Law4269 : ∀ v : Magma.tup7R12,
    ¬ @Equation4269 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4269) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4269) (by native_decide) v.1 v.2
    ((@Law4269.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4271 takes them (40 nodes). -/
def ordS7R12_Law4271 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4271. -/
theorem noS7R12_Law4271 : ∀ v : Magma.tup7R12,
    ¬ @Equation4271 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4271) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4271) (by native_decide) v.1 v.2
    ((@Law4271.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4273 takes them (232 nodes). -/
def ordS7R12_Law4273 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4273. -/
theorem noS7R12_Law4273 : ∀ v : Magma.tup7R12,
    ¬ @Equation4273 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4273) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4273) (by native_decide) v.1 v.2
    ((@Law4273.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4278 takes them (40 nodes). -/
def ordS7R12_Law4278 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4278. -/
theorem noS7R12_Law4278 : ∀ v : Magma.tup7R12,
    ¬ @Equation4278 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4278) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4278) (by native_decide) v.1 v.2
    ((@Law4278.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4279 takes them (194 nodes). -/
def ordS7R12_Law4279 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4279. -/
theorem noS7R12_Law4279 : ∀ v : Magma.tup7R12,
    ¬ @Equation4279 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4279) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4279) (by native_decide) v.1 v.2
    ((@Law4279.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (584 nodes). -/
def ordS7R12_Law4283 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4283. -/
theorem noS7R12_Law4283 : ∀ v : Magma.tup7R12,
    ¬ @Equation4283 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4285 takes them (44 nodes). -/
def ordS7R12_Law4285 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4285. -/
theorem noS7R12_Law4285 : ∀ v : Magma.tup7R12,
    ¬ @Equation4285 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4285) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4285) (by native_decide) v.1 v.2
    ((@Law4285.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4286 takes them (90 nodes). -/
def ordS7R12_Law4286 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4286. -/
theorem noS7R12_Law4286 : ∀ v : Magma.tup7R12,
    ¬ @Equation4286 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4286) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4286) (by native_decide) v.1 v.2
    ((@Law4286.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4287 takes them (62 nodes). -/
def ordS7R12_Law4287 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4287. -/
theorem noS7R12_Law4287 : ∀ v : Magma.tup7R12,
    ¬ @Equation4287 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4287) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4287) (by native_decide) v.1 v.2
    ((@Law4287.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4289 takes them (28 nodes). -/
def ordS7R12_Law4289 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4289. -/
theorem noS7R12_Law4289 : ∀ v : Magma.tup7R12,
    ¬ @Equation4289 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4289) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4289) (by native_decide) v.1 v.2
    ((@Law4289.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (270 nodes). -/
def ordS7R12_Law4291 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4291. -/
theorem noS7R12_Law4291 : ∀ v : Magma.tup7R12,
    ¬ @Equation4291 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4296 takes them (62 nodes). -/
def ordS7R12_Law4296 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4296. -/
theorem noS7R12_Law4296 : ∀ v : Magma.tup7R12,
    ¬ @Equation4296 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4296) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4296) (by native_decide) v.1 v.2
    ((@Law4296.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4300 takes them (40 nodes). -/
def ordS7R12_Law4300 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4300. -/
theorem noS7R12_Law4300 : ∀ v : Magma.tup7R12,
    ¬ @Equation4300 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4300) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4300) (by native_decide) v.1 v.2
    ((@Law4300.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4301 takes them (38 nodes). -/
def ordS7R12_Law4301 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4301. -/
theorem noS7R12_Law4301 : ∀ v : Magma.tup7R12,
    ¬ @Equation4301 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4301) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4301) (by native_decide) v.1 v.2
    ((@Law4301.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4305 takes them (47 nodes). -/
def ordS7R12_Law4305 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4305. -/
theorem noS7R12_Law4305 : ∀ v : Magma.tup7R12,
    ¬ @Equation4305 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4305) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4305) (by native_decide) v.1 v.2
    ((@Law4305.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `18` equations. -/
theorem srch7R12_refutes_46 :
    FamilyRefutes Magma.srch7R12 [
      4209, 4229, 4243, 4269, 4271, 4273, 4278, 4279, 4283, 4285, 4286, 4287, 4289, 4291, 4296,
      4300, 4301, 4305
    ] :=
  ⟨noS7R12_Law4209, noS7R12_Law4229, noS7R12_Law4243, noS7R12_Law4269, noS7R12_Law4271, noS7R12_Law4273, noS7R12_Law4278, noS7R12_Law4279, noS7R12_Law4283, noS7R12_Law4285, noS7R12_Law4286, noS7R12_Law4287, noS7R12_Law4289, noS7R12_Law4291, noS7R12_Law4296, noS7R12_Law4300, noS7R12_Law4301, noS7R12_Law4305⟩

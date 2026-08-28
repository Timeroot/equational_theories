import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 14 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `80` equations here, 760 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4264 takes them (6 nodes). -/
def ordS8R164_Law4264 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4264. -/
theorem noS8R164_Law4264 : ∀ v : Magma.tup8R164,
    ¬ @Equation4264 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4264) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4264) (by native_decide) v.1 v.2
    ((@Law4264.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4265 takes them (6 nodes). -/
def ordS8R164_Law4265 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4265. -/
theorem noS8R164_Law4265 : ∀ v : Magma.tup8R164,
    ¬ @Equation4265 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4265) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4265) (by native_decide) v.1 v.2
    ((@Law4265.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4266 takes them (6 nodes). -/
def ordS8R164_Law4266 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4266. -/
theorem noS8R164_Law4266 : ∀ v : Magma.tup8R164,
    ¬ @Equation4266 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4266) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4266) (by native_decide) v.1 v.2
    ((@Law4266.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4267 takes them (6 nodes). -/
def ordS8R164_Law4267 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4267. -/
theorem noS8R164_Law4267 : ∀ v : Magma.tup8R164,
    ¬ @Equation4267 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4267) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law4267) (by native_decide) v.1 v.2
    ((@Law4267.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4268 takes them (11 nodes). -/
def ordS8R164_Law4268 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4268. -/
theorem noS8R164_Law4268 : ∀ v : Magma.tup8R164,
    ¬ @Equation4268 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4268) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4268) (by native_decide) v.1 v.2
    ((@Law4268.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4269 takes them (23 nodes). -/
def ordS8R164_Law4269 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4269. -/
theorem noS8R164_Law4269 : ∀ v : Magma.tup8R164,
    ¬ @Equation4269 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4269) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4269) (by native_decide) v.1 v.2
    ((@Law4269.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4271 takes them (9 nodes). -/
def ordS8R164_Law4271 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4271. -/
theorem noS8R164_Law4271 : ∀ v : Magma.tup8R164,
    ¬ @Equation4271 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4271) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4271) (by native_decide) v.1 v.2
    ((@Law4271.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4274 takes them (6 nodes). -/
def ordS8R164_Law4274 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4274. -/
theorem noS8R164_Law4274 : ∀ v : Magma.tup8R164,
    ¬ @Equation4274 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4274) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4274) (by native_decide) v.1 v.2
    ((@Law4274.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4277 takes them (8 nodes). -/
def ordS8R164_Law4277 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4277. -/
theorem noS8R164_Law4277 : ∀ v : Magma.tup8R164,
    ¬ @Equation4277 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4277) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4277) (by native_decide) v.1 v.2
    ((@Law4277.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4278 takes them (10 nodes). -/
def ordS8R164_Law4278 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4278. -/
theorem noS8R164_Law4278 : ∀ v : Magma.tup8R164,
    ¬ @Equation4278 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4278) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4278) (by native_decide) v.1 v.2
    ((@Law4278.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4279 takes them (12 nodes). -/
def ordS8R164_Law4279 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4279. -/
theorem noS8R164_Law4279 : ∀ v : Magma.tup8R164,
    ¬ @Equation4279 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4279) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4279) (by native_decide) v.1 v.2
    ((@Law4279.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4281 takes them (6 nodes). -/
def ordS8R164_Law4281 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4281. -/
theorem noS8R164_Law4281 : ∀ v : Magma.tup8R164,
    ¬ @Equation4281 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4281) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4281) (by native_decide) v.1 v.2
    ((@Law4281.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4282 takes them (11 nodes). -/
def ordS8R164_Law4282 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4282. -/
theorem noS8R164_Law4282 : ∀ v : Magma.tup8R164,
    ¬ @Equation4282 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4282) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4282) (by native_decide) v.1 v.2
    ((@Law4282.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4284 takes them (25 nodes). -/
def ordS8R164_Law4284 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4284. -/
theorem noS8R164_Law4284 : ∀ v : Magma.tup8R164,
    ¬ @Equation4284 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4284) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4284) (by native_decide) v.1 v.2
    ((@Law4284.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4285 takes them (9 nodes). -/
def ordS8R164_Law4285 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4285. -/
theorem noS8R164_Law4285 : ∀ v : Magma.tup8R164,
    ¬ @Equation4285 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4285) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4285) (by native_decide) v.1 v.2
    ((@Law4285.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4286 takes them (10 nodes). -/
def ordS8R164_Law4286 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4286. -/
theorem noS8R164_Law4286 : ∀ v : Magma.tup8R164,
    ¬ @Equation4286 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4286) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4286) (by native_decide) v.1 v.2
    ((@Law4286.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4287 takes them (13 nodes). -/
def ordS8R164_Law4287 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4287. -/
theorem noS8R164_Law4287 : ∀ v : Magma.tup8R164,
    ¬ @Equation4287 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4287) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4287) (by native_decide) v.1 v.2
    ((@Law4287.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4288 takes them (10 nodes). -/
def ordS8R164_Law4288 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4288. -/
theorem noS8R164_Law4288 : ∀ v : Magma.tup8R164,
    ¬ @Equation4288 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4288) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4288) (by native_decide) v.1 v.2
    ((@Law4288.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4289 takes them (9 nodes). -/
def ordS8R164_Law4289 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4289. -/
theorem noS8R164_Law4289 : ∀ v : Magma.tup8R164,
    ¬ @Equation4289 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4289) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4289) (by native_decide) v.1 v.2
    ((@Law4289.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (17 nodes). -/
def ordS8R164_Law4291 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4291. -/
theorem noS8R164_Law4291 : ∀ v : Magma.tup8R164,
    ¬ @Equation4291 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4292 takes them (6 nodes). -/
def ordS8R164_Law4292 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4292. -/
theorem noS8R164_Law4292 : ∀ v : Magma.tup8R164,
    ¬ @Equation4292 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4292) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4292) (by native_decide) v.1 v.2
    ((@Law4292.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4293 takes them (15 nodes). -/
def ordS8R164_Law4293 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4293. -/
theorem noS8R164_Law4293 : ∀ v : Magma.tup8R164,
    ¬ @Equation4293 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4293) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4293) (by native_decide) v.1 v.2
    ((@Law4293.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4294 takes them (8 nodes). -/
def ordS8R164_Law4294 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4294. -/
theorem noS8R164_Law4294 : ∀ v : Magma.tup8R164,
    ¬ @Equation4294 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4294) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4294) (by native_decide) v.1 v.2
    ((@Law4294.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4295 takes them (7 nodes). -/
def ordS8R164_Law4295 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4295. -/
theorem noS8R164_Law4295 : ∀ v : Magma.tup8R164,
    ¬ @Equation4295 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4295) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4295) (by native_decide) v.1 v.2
    ((@Law4295.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4296 takes them (10 nodes). -/
def ordS8R164_Law4296 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4296. -/
theorem noS8R164_Law4296 : ∀ v : Magma.tup8R164,
    ¬ @Equation4296 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4296) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4296) (by native_decide) v.1 v.2
    ((@Law4296.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4298 takes them (6 nodes). -/
def ordS8R164_Law4298 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4298. -/
theorem noS8R164_Law4298 : ∀ v : Magma.tup8R164,
    ¬ @Equation4298 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4298) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4298) (by native_decide) v.1 v.2
    ((@Law4298.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4299 takes them (7 nodes). -/
def ordS8R164_Law4299 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4299. -/
theorem noS8R164_Law4299 : ∀ v : Magma.tup8R164,
    ¬ @Equation4299 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4299) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4299) (by native_decide) v.1 v.2
    ((@Law4299.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4300 takes them (10 nodes). -/
def ordS8R164_Law4300 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4300. -/
theorem noS8R164_Law4300 : ∀ v : Magma.tup8R164,
    ¬ @Equation4300 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4300) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4300) (by native_decide) v.1 v.2
    ((@Law4300.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4301 takes them (6 nodes). -/
def ordS8R164_Law4301 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4301. -/
theorem noS8R164_Law4301 : ∀ v : Magma.tup8R164,
    ¬ @Equation4301 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4301) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4301) (by native_decide) v.1 v.2
    ((@Law4301.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4302 takes them (6 nodes). -/
def ordS8R164_Law4302 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4302. -/
theorem noS8R164_Law4302 : ∀ v : Magma.tup8R164,
    ¬ @Equation4302 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4302) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4302) (by native_decide) v.1 v.2
    ((@Law4302.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4303 takes them (7 nodes). -/
def ordS8R164_Law4303 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4303. -/
theorem noS8R164_Law4303 : ∀ v : Magma.tup8R164,
    ¬ @Equation4303 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4303) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4303) (by native_decide) v.1 v.2
    ((@Law4303.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4304 takes them (11 nodes). -/
def ordS8R164_Law4304 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4304. -/
theorem noS8R164_Law4304 : ∀ v : Magma.tup8R164,
    ¬ @Equation4304 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4304) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4304) (by native_decide) v.1 v.2
    ((@Law4304.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4306 takes them (6 nodes). -/
def ordS8R164_Law4306 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4306. -/
theorem noS8R164_Law4306 : ∀ v : Magma.tup8R164,
    ¬ @Equation4306 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4306) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4306) (by native_decide) v.1 v.2
    ((@Law4306.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4308 takes them (8 nodes). -/
def ordS8R164_Law4308 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4308. -/
theorem noS8R164_Law4308 : ∀ v : Magma.tup8R164,
    ¬ @Equation4308 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4308) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4308) (by native_decide) v.1 v.2
    ((@Law4308.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4309 takes them (6 nodes). -/
def ordS8R164_Law4309 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4309. -/
theorem noS8R164_Law4309 : ∀ v : Magma.tup8R164,
    ¬ @Equation4309 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4309) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4309) (by native_decide) v.1 v.2
    ((@Law4309.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4310 takes them (10 nodes). -/
def ordS8R164_Law4310 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4310. -/
theorem noS8R164_Law4310 : ∀ v : Magma.tup8R164,
    ¬ @Equation4310 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4311 takes them (6 nodes). -/
def ordS8R164_Law4311 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4311. -/
theorem noS8R164_Law4311 : ∀ v : Magma.tup8R164,
    ¬ @Equation4311 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4311) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4311) (by native_decide) v.1 v.2
    ((@Law4311.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4312 takes them (7 nodes). -/
def ordS8R164_Law4312 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4312. -/
theorem noS8R164_Law4312 : ∀ v : Magma.tup8R164,
    ¬ @Equation4312 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4312) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4312) (by native_decide) v.1 v.2
    ((@Law4312.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4313 takes them (6 nodes). -/
def ordS8R164_Law4313 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4313. -/
theorem noS8R164_Law4313 : ∀ v : Magma.tup8R164,
    ¬ @Equation4313 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4313) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4313) (by native_decide) v.1 v.2
    ((@Law4313.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (24 nodes). -/
def ordS8R164_Law4314 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4314. -/
theorem noS8R164_Law4314 : ∀ v : Magma.tup8R164,
    ¬ @Equation4314 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (9 nodes). -/
def ordS8R164_Law4315 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4315. -/
theorem noS8R164_Law4315 : ∀ v : Magma.tup8R164,
    ¬ @Equation4315 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4316 takes them (23 nodes). -/
def ordS8R164_Law4316 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4316. -/
theorem noS8R164_Law4316 : ∀ v : Magma.tup8R164,
    ¬ @Equation4316 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4316) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4316) (by native_decide) v.1 v.2
    ((@Law4316.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4317 takes them (10 nodes). -/
def ordS8R164_Law4317 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4317. -/
theorem noS8R164_Law4317 : ∀ v : Magma.tup8R164,
    ¬ @Equation4317 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4317) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4317) (by native_decide) v.1 v.2
    ((@Law4317.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4318 takes them (18 nodes). -/
def ordS8R164_Law4318 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4318. -/
theorem noS8R164_Law4318 : ∀ v : Magma.tup8R164,
    ¬ @Equation4318 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4318) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4318) (by native_decide) v.1 v.2
    ((@Law4318.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4319 takes them (9 nodes). -/
def ordS8R164_Law4319 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4319. -/
theorem noS8R164_Law4319 : ∀ v : Magma.tup8R164,
    ¬ @Equation4319 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4319) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4319) (by native_decide) v.1 v.2
    ((@Law4319.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4321 takes them (16 nodes). -/
def ordS8R164_Law4321 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4321. -/
theorem noS8R164_Law4321 : ∀ v : Magma.tup8R164,
    ¬ @Equation4321 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4321) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4321) (by native_decide) v.1 v.2
    ((@Law4321.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4322 takes them (6 nodes). -/
def ordS8R164_Law4322 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4322. -/
theorem noS8R164_Law4322 : ∀ v : Magma.tup8R164,
    ¬ @Equation4322 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4322) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4322) (by native_decide) v.1 v.2
    ((@Law4322.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4323 takes them (10 nodes). -/
def ordS8R164_Law4323 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4323. -/
theorem noS8R164_Law4323 : ∀ v : Magma.tup8R164,
    ¬ @Equation4323 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4324 takes them (12 nodes). -/
def ordS8R164_Law4324 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4324. -/
theorem noS8R164_Law4324 : ∀ v : Magma.tup8R164,
    ¬ @Equation4324 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4324) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4324) (by native_decide) v.1 v.2
    ((@Law4324.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4326 takes them (6 nodes). -/
def ordS8R164_Law4326 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4326. -/
theorem noS8R164_Law4326 : ∀ v : Magma.tup8R164,
    ¬ @Equation4326 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4326) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4326) (by native_decide) v.1 v.2
    ((@Law4326.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4327 takes them (14 nodes). -/
def ordS8R164_Law4327 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4327. -/
theorem noS8R164_Law4327 : ∀ v : Magma.tup8R164,
    ¬ @Equation4327 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4327) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4327) (by native_decide) v.1 v.2
    ((@Law4327.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4328 takes them (7 nodes). -/
def ordS8R164_Law4328 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4328. -/
theorem noS8R164_Law4328 : ∀ v : Magma.tup8R164,
    ¬ @Equation4328 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4328) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4328) (by native_decide) v.1 v.2
    ((@Law4328.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4329 takes them (6 nodes). -/
def ordS8R164_Law4329 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4329. -/
theorem noS8R164_Law4329 : ∀ v : Magma.tup8R164,
    ¬ @Equation4329 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4329) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4329) (by native_decide) v.1 v.2
    ((@Law4329.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4330 takes them (10 nodes). -/
def ordS8R164_Law4330 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4330. -/
theorem noS8R164_Law4330 : ∀ v : Magma.tup8R164,
    ¬ @Equation4330 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4330) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4330) (by native_decide) v.1 v.2
    ((@Law4330.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4331 takes them (12 nodes). -/
def ordS8R164_Law4331 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4331. -/
theorem noS8R164_Law4331 : ∀ v : Magma.tup8R164,
    ¬ @Equation4331 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4331) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4331) (by native_decide) v.1 v.2
    ((@Law4331.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4333 takes them (6 nodes). -/
def ordS8R164_Law4333 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4333. -/
theorem noS8R164_Law4333 : ∀ v : Magma.tup8R164,
    ¬ @Equation4333 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4333) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4333) (by native_decide) v.1 v.2
    ((@Law4333.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4334 takes them (10 nodes). -/
def ordS8R164_Law4334 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4334. -/
theorem noS8R164_Law4334 : ∀ v : Magma.tup8R164,
    ¬ @Equation4334 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4334) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4334) (by native_decide) v.1 v.2
    ((@Law4334.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4335 takes them (7 nodes). -/
def ordS8R164_Law4335 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4335. -/
theorem noS8R164_Law4335 : ∀ v : Magma.tup8R164,
    ¬ @Equation4335 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4335) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4335) (by native_decide) v.1 v.2
    ((@Law4335.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4336 takes them (12 nodes). -/
def ordS8R164_Law4336 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4336. -/
theorem noS8R164_Law4336 : ∀ v : Magma.tup8R164,
    ¬ @Equation4336 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4336) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4336) (by native_decide) v.1 v.2
    ((@Law4336.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4337 takes them (12 nodes). -/
def ordS8R164_Law4337 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4337. -/
theorem noS8R164_Law4337 : ∀ v : Magma.tup8R164,
    ¬ @Equation4337 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4337) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4337) (by native_decide) v.1 v.2
    ((@Law4337.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4338 takes them (6 nodes). -/
def ordS8R164_Law4338 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4338. -/
theorem noS8R164_Law4338 : ∀ v : Magma.tup8R164,
    ¬ @Equation4338 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4338) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4338) (by native_decide) v.1 v.2
    ((@Law4338.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (9 nodes). -/
def ordS8R164_Law4339 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4339. -/
theorem noS8R164_Law4339 : ∀ v : Magma.tup8R164,
    ¬ @Equation4339 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4340 takes them (13 nodes). -/
def ordS8R164_Law4340 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4340. -/
theorem noS8R164_Law4340 : ∀ v : Magma.tup8R164,
    ¬ @Equation4340 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4340) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4340) (by native_decide) v.1 v.2
    ((@Law4340.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4342 takes them (9 nodes). -/
def ordS8R164_Law4342 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4342. -/
theorem noS8R164_Law4342 : ∀ v : Magma.tup8R164,
    ¬ @Equation4342 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4342) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4342) (by native_decide) v.1 v.2
    ((@Law4342.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4344 takes them (6 nodes). -/
def ordS8R164_Law4344 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4344. -/
theorem noS8R164_Law4344 : ∀ v : Magma.tup8R164,
    ¬ @Equation4344 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4344) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4344) (by native_decide) v.1 v.2
    ((@Law4344.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4345 takes them (7 nodes). -/
def ordS8R164_Law4345 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4345. -/
theorem noS8R164_Law4345 : ∀ v : Magma.tup8R164,
    ¬ @Equation4345 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4345) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4345) (by native_decide) v.1 v.2
    ((@Law4345.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4347 takes them (6 nodes). -/
def ordS8R164_Law4347 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4347. -/
theorem noS8R164_Law4347 : ∀ v : Magma.tup8R164,
    ¬ @Equation4347 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4347) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4347) (by native_decide) v.1 v.2
    ((@Law4347.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4348 takes them (10 nodes). -/
def ordS8R164_Law4348 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4348. -/
theorem noS8R164_Law4348 : ∀ v : Magma.tup8R164,
    ¬ @Equation4348 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4349 takes them (6 nodes). -/
def ordS8R164_Law4349 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4349. -/
theorem noS8R164_Law4349 : ∀ v : Magma.tup8R164,
    ¬ @Equation4349 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4349) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4349) (by native_decide) v.1 v.2
    ((@Law4349.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4350 takes them (7 nodes). -/
def ordS8R164_Law4350 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4350. -/
theorem noS8R164_Law4350 : ∀ v : Magma.tup8R164,
    ¬ @Equation4350 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4350) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4350) (by native_decide) v.1 v.2
    ((@Law4350.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4352 takes them (6 nodes). -/
def ordS8R164_Law4352 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4352. -/
theorem noS8R164_Law4352 : ∀ v : Magma.tup8R164,
    ¬ @Equation4352 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4352) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4352) (by native_decide) v.1 v.2
    ((@Law4352.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4353 takes them (7 nodes). -/
def ordS8R164_Law4353 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4353. -/
theorem noS8R164_Law4353 : ∀ v : Magma.tup8R164,
    ¬ @Equation4353 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4353) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4353) (by native_decide) v.1 v.2
    ((@Law4353.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (10 nodes). -/
def ordS8R164_Law4354 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4354. -/
theorem noS8R164_Law4354 : ∀ v : Magma.tup8R164,
    ¬ @Equation4354 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4356 takes them (6 nodes). -/
def ordS8R164_Law4356 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4356. -/
theorem noS8R164_Law4356 : ∀ v : Magma.tup8R164,
    ¬ @Equation4356 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4356) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4356) (by native_decide) v.1 v.2
    ((@Law4356.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (9 nodes). -/
def ordS8R164_Law4357 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4357. -/
theorem noS8R164_Law4357 : ∀ v : Magma.tup8R164,
    ¬ @Equation4357 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4359 takes them (9 nodes). -/
def ordS8R164_Law4359 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4359. -/
theorem noS8R164_Law4359 : ∀ v : Magma.tup8R164,
    ¬ @Equation4359 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4359) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4359) (by native_decide) v.1 v.2
    ((@Law4359.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4360 takes them (13 nodes). -/
def ordS8R164_Law4360 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4360. -/
theorem noS8R164_Law4360 : ∀ v : Magma.tup8R164,
    ¬ @Equation4360 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4360) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4360) (by native_decide) v.1 v.2
    ((@Law4360.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4361 takes them (9 nodes). -/
def ordS8R164_Law4361 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4361. -/
theorem noS8R164_Law4361 : ∀ v : Magma.tup8R164,
    ¬ @Equation4361 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4361) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4361) (by native_decide) v.1 v.2
    ((@Law4361.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4363 takes them (6 nodes). -/
def ordS8R164_Law4363 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4363. -/
theorem noS8R164_Law4363 : ∀ v : Magma.tup8R164,
    ¬ @Equation4363 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4363) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4363) (by native_decide) v.1 v.2
    ((@Law4363.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4365 takes them (6 nodes). -/
def ordS8R164_Law4365 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4365. -/
theorem noS8R164_Law4365 : ∀ v : Magma.tup8R164,
    ¬ @Equation4365 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4365) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4365) (by native_decide) v.1 v.2
    ((@Law4365.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `80` equations. -/
theorem srch8R164_refutes_13 :
    FamilyRefutes Magma.srch8R164 [
      4264, 4265, 4266, 4267, 4268, 4269, 4271, 4274, 4277, 4278, 4279, 4281, 4282, 4284, 4285,
      4286, 4287, 4288, 4289, 4291, 4292, 4293, 4294, 4295, 4296, 4298, 4299, 4300, 4301, 4302,
      4303, 4304, 4306, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315, 4316, 4317, 4318, 4319,
      4321, 4322, 4323, 4324, 4326, 4327, 4328, 4329, 4330, 4331, 4333, 4334, 4335, 4336, 4337,
      4338, 4339, 4340, 4342, 4344, 4345, 4347, 4348, 4349, 4350, 4352, 4353, 4354, 4356, 4357,
      4359, 4360, 4361, 4363, 4365
    ] :=
  ⟨noS8R164_Law4264, noS8R164_Law4265, noS8R164_Law4266, noS8R164_Law4267, noS8R164_Law4268, noS8R164_Law4269, noS8R164_Law4271, noS8R164_Law4274, noS8R164_Law4277, noS8R164_Law4278, noS8R164_Law4279, noS8R164_Law4281, noS8R164_Law4282, noS8R164_Law4284, noS8R164_Law4285, noS8R164_Law4286, noS8R164_Law4287, noS8R164_Law4288, noS8R164_Law4289, noS8R164_Law4291, noS8R164_Law4292, noS8R164_Law4293, noS8R164_Law4294, noS8R164_Law4295, noS8R164_Law4296, noS8R164_Law4298, noS8R164_Law4299, noS8R164_Law4300, noS8R164_Law4301, noS8R164_Law4302, noS8R164_Law4303, noS8R164_Law4304, noS8R164_Law4306, noS8R164_Law4308, noS8R164_Law4309, noS8R164_Law4310, noS8R164_Law4311, noS8R164_Law4312, noS8R164_Law4313, noS8R164_Law4314, noS8R164_Law4315, noS8R164_Law4316, noS8R164_Law4317, noS8R164_Law4318, noS8R164_Law4319, noS8R164_Law4321, noS8R164_Law4322, noS8R164_Law4323, noS8R164_Law4324, noS8R164_Law4326, noS8R164_Law4327, noS8R164_Law4328, noS8R164_Law4329, noS8R164_Law4330, noS8R164_Law4331, noS8R164_Law4333, noS8R164_Law4334, noS8R164_Law4335, noS8R164_Law4336, noS8R164_Law4337, noS8R164_Law4338, noS8R164_Law4339, noS8R164_Law4340, noS8R164_Law4342, noS8R164_Law4344, noS8R164_Law4345, noS8R164_Law4347, noS8R164_Law4348, noS8R164_Law4349, noS8R164_Law4350, noS8R164_Law4352, noS8R164_Law4353, noS8R164_Law4354, noS8R164_Law4356, noS8R164_Law4357, noS8R164_Law4359, noS8R164_Law4360, noS8R164_Law4361, noS8R164_Law4363, noS8R164_Law4365⟩

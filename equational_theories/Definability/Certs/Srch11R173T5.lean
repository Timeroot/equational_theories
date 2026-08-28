import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 6 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 297 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3256 takes them (3 nodes). -/
def ordS11R173_Law3256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3256. -/
theorem noS11R173_Law3256 : ∀ v : Magma.tup11R173,
    ¬ @Equation3256 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3256) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3256) (by native_decide) v.1 v.2
    ((@Law3256.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3257 takes them (3 nodes). -/
def ordS11R173_Law3257 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3257. -/
theorem noS11R173_Law3257 : ∀ v : Magma.tup11R173,
    ¬ @Equation3257 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3257) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3257) (by native_decide) v.1 v.2
    ((@Law3257.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3258 takes them (4 nodes). -/
def ordS11R173_Law3258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3258. -/
theorem noS11R173_Law3258 : ∀ v : Magma.tup11R173,
    ¬ @Equation3258 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3258) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3258) (by native_decide) v.1 v.2
    ((@Law3258.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (3 nodes). -/
def ordS11R173_Law3259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3259. -/
theorem noS11R173_Law3259 : ∀ v : Magma.tup11R173,
    ¬ @Equation3259 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3260 takes them (3 nodes). -/
def ordS11R173_Law3260 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3260. -/
theorem noS11R173_Law3260 : ∀ v : Magma.tup11R173,
    ¬ @Equation3260 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3260) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3260) (by native_decide) v.1 v.2
    ((@Law3260.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3262 takes them (3 nodes). -/
def ordS11R173_Law3262 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3262. -/
theorem noS11R173_Law3262 : ∀ v : Magma.tup11R173,
    ¬ @Equation3262 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3262) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3262) (by native_decide) v.1 v.2
    ((@Law3262.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3263 takes them (3 nodes). -/
def ordS11R173_Law3263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3263. -/
theorem noS11R173_Law3263 : ∀ v : Magma.tup11R173,
    ¬ @Equation3263 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3263) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3263) (by native_decide) v.1 v.2
    ((@Law3263.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3264 takes them (4 nodes). -/
def ordS11R173_Law3264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3264. -/
theorem noS11R173_Law3264 : ∀ v : Magma.tup11R173,
    ¬ @Equation3264 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3264) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3264) (by native_decide) v.1 v.2
    ((@Law3264.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (3 nodes). -/
def ordS11R173_Law3265 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3265. -/
theorem noS11R173_Law3265 : ∀ v : Magma.tup11R173,
    ¬ @Equation3265 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3266 takes them (3 nodes). -/
def ordS11R173_Law3266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3266. -/
theorem noS11R173_Law3266 : ∀ v : Magma.tup11R173,
    ¬ @Equation3266 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3266) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3266) (by native_decide) v.1 v.2
    ((@Law3266.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3267 takes them (3 nodes). -/
def ordS11R173_Law3267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3267. -/
theorem noS11R173_Law3267 : ∀ v : Magma.tup11R173,
    ¬ @Equation3267 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3267) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3267) (by native_decide) v.1 v.2
    ((@Law3267.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3271 takes them (3 nodes). -/
def ordS11R173_Law3271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3271. -/
theorem noS11R173_Law3271 : ∀ v : Magma.tup11R173,
    ¬ @Equation3271 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3271) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3271) (by native_decide) v.1 v.2
    ((@Law3271.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3281 takes them (3 nodes). -/
def ordS11R173_Law3281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3281. -/
theorem noS11R173_Law3281 : ∀ v : Magma.tup11R173,
    ¬ @Equation3281 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3305 takes them (3 nodes). -/
def ordS11R173_Law3305 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3305. -/
theorem noS11R173_Law3305 : ∀ v : Magma.tup11R173,
    ¬ @Equation3305 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3305) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3305) (by native_decide) v.1 v.2
    ((@Law3305.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3307 takes them (3 nodes). -/
def ordS11R173_Law3307 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3307. -/
theorem noS11R173_Law3307 : ∀ v : Magma.tup11R173,
    ¬ @Equation3307 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3307) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3307) (by native_decide) v.1 v.2
    ((@Law3307.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (3 nodes). -/
def ordS11R173_Law3308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3308. -/
theorem noS11R173_Law3308 : ∀ v : Magma.tup11R173,
    ¬ @Equation3308 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3309 takes them (4 nodes). -/
def ordS11R173_Law3309 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3309. -/
theorem noS11R173_Law3309 : ∀ v : Magma.tup11R173,
    ¬ @Equation3309 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3309) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3309) (by native_decide) v.1 v.2
    ((@Law3309.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3310 takes them (3 nodes). -/
def ordS11R173_Law3310 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3310. -/
theorem noS11R173_Law3310 : ∀ v : Magma.tup11R173,
    ¬ @Equation3310 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3310) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3310) (by native_decide) v.1 v.2
    ((@Law3310.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3311 takes them (3 nodes). -/
def ordS11R173_Law3311 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3311. -/
theorem noS11R173_Law3311 : ∀ v : Magma.tup11R173,
    ¬ @Equation3311 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3311) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3311) (by native_decide) v.1 v.2
    ((@Law3311.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3312 takes them (4 nodes). -/
def ordS11R173_Law3312 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3312. -/
theorem noS11R173_Law3312 : ∀ v : Magma.tup11R173,
    ¬ @Equation3312 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3312) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3312) (by native_decide) v.1 v.2
    ((@Law3312.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3313 takes them (3 nodes). -/
def ordS11R173_Law3313 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3313. -/
theorem noS11R173_Law3313 : ∀ v : Magma.tup11R173,
    ¬ @Equation3313 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3313) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3313) (by native_decide) v.1 v.2
    ((@Law3313.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3314 takes them (3 nodes). -/
def ordS11R173_Law3314 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3314. -/
theorem noS11R173_Law3314 : ∀ v : Magma.tup11R173,
    ¬ @Equation3314 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3314) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3314) (by native_decide) v.1 v.2
    ((@Law3314.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3315 takes them (3 nodes). -/
def ordS11R173_Law3315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3315. -/
theorem noS11R173_Law3315 : ∀ v : Magma.tup11R173,
    ¬ @Equation3315 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3315) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3315) (by native_decide) v.1 v.2
    ((@Law3315.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3316 takes them (4 nodes). -/
def ordS11R173_Law3316 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3316. -/
theorem noS11R173_Law3316 : ∀ v : Magma.tup11R173,
    ¬ @Equation3316 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3316) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3316) (by native_decide) v.1 v.2
    ((@Law3316.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3317 takes them (3 nodes). -/
def ordS11R173_Law3317 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3317. -/
theorem noS11R173_Law3317 : ∀ v : Magma.tup11R173,
    ¬ @Equation3317 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3317) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3317) (by native_decide) v.1 v.2
    ((@Law3317.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3318 takes them (3 nodes). -/
def ordS11R173_Law3318 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3318. -/
theorem noS11R173_Law3318 : ∀ v : Magma.tup11R173,
    ¬ @Equation3318 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3318) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3318) (by native_decide) v.1 v.2
    ((@Law3318.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3320 takes them (3 nodes). -/
def ordS11R173_Law3320 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3320. -/
theorem noS11R173_Law3320 : ∀ v : Magma.tup11R173,
    ¬ @Equation3320 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3320) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3320) (by native_decide) v.1 v.2
    ((@Law3320.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (3 nodes). -/
def ordS11R173_Law3321 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3321. -/
theorem noS11R173_Law3321 : ∀ v : Magma.tup11R173,
    ¬ @Equation3321 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3322 takes them (4 nodes). -/
def ordS11R173_Law3322 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3322. -/
theorem noS11R173_Law3322 : ∀ v : Magma.tup11R173,
    ¬ @Equation3322 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3322) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3322) (by native_decide) v.1 v.2
    ((@Law3322.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3323 takes them (3 nodes). -/
def ordS11R173_Law3323 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3323. -/
theorem noS11R173_Law3323 : ∀ v : Magma.tup11R173,
    ¬ @Equation3323 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3323) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3323) (by native_decide) v.1 v.2
    ((@Law3323.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (3 nodes). -/
def ordS11R173_Law3324 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3324. -/
theorem noS11R173_Law3324 : ∀ v : Magma.tup11R173,
    ¬ @Equation3324 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3325 takes them (3 nodes). -/
def ordS11R173_Law3325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3325. -/
theorem noS11R173_Law3325 : ∀ v : Magma.tup11R173,
    ¬ @Equation3325 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3325) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3325) (by native_decide) v.1 v.2
    ((@Law3325.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (4 nodes). -/
def ordS11R173_Law3326 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3326. -/
theorem noS11R173_Law3326 : ∀ v : Magma.tup11R173,
    ¬ @Equation3326 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3327 takes them (3 nodes). -/
def ordS11R173_Law3327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3327. -/
theorem noS11R173_Law3327 : ∀ v : Magma.tup11R173,
    ¬ @Equation3327 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3327) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3327) (by native_decide) v.1 v.2
    ((@Law3327.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3328 takes them (3 nodes). -/
def ordS11R173_Law3328 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3328. -/
theorem noS11R173_Law3328 : ∀ v : Magma.tup11R173,
    ¬ @Equation3328 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3328) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3328) (by native_decide) v.1 v.2
    ((@Law3328.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3329 takes them (3 nodes). -/
def ordS11R173_Law3329 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3329. -/
theorem noS11R173_Law3329 : ∀ v : Magma.tup11R173,
    ¬ @Equation3329 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3329) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3329) (by native_decide) v.1 v.2
    ((@Law3329.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3330 takes them (4 nodes). -/
def ordS11R173_Law3330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3330. -/
theorem noS11R173_Law3330 : ∀ v : Magma.tup11R173,
    ¬ @Equation3330 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3330) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3330) (by native_decide) v.1 v.2
    ((@Law3330.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (3 nodes). -/
def ordS11R173_Law3331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3331. -/
theorem noS11R173_Law3331 : ∀ v : Magma.tup11R173,
    ¬ @Equation3331 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3332 takes them (3 nodes). -/
def ordS11R173_Law3332 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3332. -/
theorem noS11R173_Law3332 : ∀ v : Magma.tup11R173,
    ¬ @Equation3332 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3332) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3332) (by native_decide) v.1 v.2
    ((@Law3332.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3333 takes them (3 nodes). -/
def ordS11R173_Law3333 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3333. -/
theorem noS11R173_Law3333 : ∀ v : Magma.tup11R173,
    ¬ @Equation3333 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3333) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3333) (by native_decide) v.1 v.2
    ((@Law3333.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3335 takes them (3 nodes). -/
def ordS11R173_Law3335 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3335. -/
theorem noS11R173_Law3335 : ∀ v : Magma.tup11R173,
    ¬ @Equation3335 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3335) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3335) (by native_decide) v.1 v.2
    ((@Law3335.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3336 takes them (3 nodes). -/
def ordS11R173_Law3336 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3336. -/
theorem noS11R173_Law3336 : ∀ v : Magma.tup11R173,
    ¬ @Equation3336 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3336) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3336) (by native_decide) v.1 v.2
    ((@Law3336.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3337 takes them (3 nodes). -/
def ordS11R173_Law3337 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3337. -/
theorem noS11R173_Law3337 : ∀ v : Magma.tup11R173,
    ¬ @Equation3337 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3337) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3337) (by native_decide) v.1 v.2
    ((@Law3337.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3338 takes them (4 nodes). -/
def ordS11R173_Law3338 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3338. -/
theorem noS11R173_Law3338 : ∀ v : Magma.tup11R173,
    ¬ @Equation3338 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3338) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3338) (by native_decide) v.1 v.2
    ((@Law3338.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3339 takes them (3 nodes). -/
def ordS11R173_Law3339 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3339. -/
theorem noS11R173_Law3339 : ∀ v : Magma.tup11R173,
    ¬ @Equation3339 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3339) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3339) (by native_decide) v.1 v.2
    ((@Law3339.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3340 takes them (3 nodes). -/
def ordS11R173_Law3340 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3340. -/
theorem noS11R173_Law3340 : ∀ v : Magma.tup11R173,
    ¬ @Equation3340 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3340) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3340) (by native_decide) v.1 v.2
    ((@Law3340.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3346 takes them (3 nodes). -/
def ordS11R173_Law3346 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3346. -/
theorem noS11R173_Law3346 : ∀ v : Magma.tup11R173,
    ¬ @Equation3346 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3346) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3346) (by native_decide) v.1 v.2
    ((@Law3346.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3388 takes them (3 nodes). -/
def ordS11R173_Law3388 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3388. -/
theorem noS11R173_Law3388 : ∀ v : Magma.tup11R173,
    ¬ @Equation3388 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3388) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3388) (by native_decide) v.1 v.2
    ((@Law3388.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3457 takes them (3 nodes). -/
def ordS11R173_Law3457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3457. -/
theorem noS11R173_Law3457 : ∀ v : Magma.tup11R173,
    ¬ @Equation3457 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3457) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3457) (by native_decide) v.1 v.2
    ((@Law3457.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (4 nodes). -/
def ordS11R173_Law3458 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3458. -/
theorem noS11R173_Law3458 : ∀ v : Magma.tup11R173,
    ¬ @Equation3458 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3460 takes them (3 nodes). -/
def ordS11R173_Law3460 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3460. -/
theorem noS11R173_Law3460 : ∀ v : Magma.tup11R173,
    ¬ @Equation3460 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3460) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3460) (by native_decide) v.1 v.2
    ((@Law3460.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3461 takes them (4 nodes). -/
def ordS11R173_Law3461 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3461. -/
theorem noS11R173_Law3461 : ∀ v : Magma.tup11R173,
    ¬ @Equation3461 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3461) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3461) (by native_decide) v.1 v.2
    ((@Law3461.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (3 nodes). -/
def ordS11R173_Law3462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3462. -/
theorem noS11R173_Law3462 : ∀ v : Magma.tup11R173,
    ¬ @Equation3462 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3463 takes them (3 nodes). -/
def ordS11R173_Law3463 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3463. -/
theorem noS11R173_Law3463 : ∀ v : Magma.tup11R173,
    ¬ @Equation3463 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3463) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3463) (by native_decide) v.1 v.2
    ((@Law3463.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3464 takes them (4 nodes). -/
def ordS11R173_Law3464 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3464. -/
theorem noS11R173_Law3464 : ∀ v : Magma.tup11R173,
    ¬ @Equation3464 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3464) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3464) (by native_decide) v.1 v.2
    ((@Law3464.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3465 takes them (3 nodes). -/
def ordS11R173_Law3465 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3465. -/
theorem noS11R173_Law3465 : ∀ v : Magma.tup11R173,
    ¬ @Equation3465 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3465) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3465) (by native_decide) v.1 v.2
    ((@Law3465.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3466 takes them (3 nodes). -/
def ordS11R173_Law3466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3466. -/
theorem noS11R173_Law3466 : ∀ v : Magma.tup11R173,
    ¬ @Equation3466 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3466) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3466) (by native_decide) v.1 v.2
    ((@Law3466.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3467 takes them (4 nodes). -/
def ordS11R173_Law3467 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3467. -/
theorem noS11R173_Law3467 : ∀ v : Magma.tup11R173,
    ¬ @Equation3467 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3467) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3467) (by native_decide) v.1 v.2
    ((@Law3467.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3468 takes them (3 nodes). -/
def ordS11R173_Law3468 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3468. -/
theorem noS11R173_Law3468 : ∀ v : Magma.tup11R173,
    ¬ @Equation3468 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3469 takes them (3 nodes). -/
def ordS11R173_Law3469 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3469. -/
theorem noS11R173_Law3469 : ∀ v : Magma.tup11R173,
    ¬ @Equation3469 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3469) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3469) (by native_decide) v.1 v.2
    ((@Law3469.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3470 takes them (3 nodes). -/
def ordS11R173_Law3470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3470. -/
theorem noS11R173_Law3470 : ∀ v : Magma.tup11R173,
    ¬ @Equation3470 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3470) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3470) (by native_decide) v.1 v.2
    ((@Law3470.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (3 nodes). -/
def ordS11R173_Law3474 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3474. -/
theorem noS11R173_Law3474 : ∀ v : Magma.tup11R173,
    ¬ @Equation3474 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3508 takes them (3 nodes). -/
def ordS11R173_Law3508 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3508. -/
theorem noS11R173_Law3508 : ∀ v : Magma.tup11R173,
    ¬ @Equation3508 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3508) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3508) (by native_decide) v.1 v.2
    ((@Law3508.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3509 takes them (4 nodes). -/
def ordS11R173_Law3509 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3509. -/
theorem noS11R173_Law3509 : ∀ v : Magma.tup11R173,
    ¬ @Equation3509 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3509) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3509) (by native_decide) v.1 v.2
    ((@Law3509.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3510 takes them (3 nodes). -/
def ordS11R173_Law3510 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3510. -/
theorem noS11R173_Law3510 : ∀ v : Magma.tup11R173,
    ¬ @Equation3510 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3510) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3510) (by native_decide) v.1 v.2
    ((@Law3510.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (3 nodes). -/
def ordS11R173_Law3511 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3511. -/
theorem noS11R173_Law3511 : ∀ v : Magma.tup11R173,
    ¬ @Equation3511 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3512 takes them (4 nodes). -/
def ordS11R173_Law3512 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3512. -/
theorem noS11R173_Law3512 : ∀ v : Magma.tup11R173,
    ¬ @Equation3512 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3512) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3512) (by native_decide) v.1 v.2
    ((@Law3512.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3513 takes them (3 nodes). -/
def ordS11R173_Law3513 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3513. -/
theorem noS11R173_Law3513 : ∀ v : Magma.tup11R173,
    ¬ @Equation3513 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3513) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3513) (by native_decide) v.1 v.2
    ((@Law3513.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3514 takes them (3 nodes). -/
def ordS11R173_Law3514 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3514. -/
theorem noS11R173_Law3514 : ∀ v : Magma.tup11R173,
    ¬ @Equation3514 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3514) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3514) (by native_decide) v.1 v.2
    ((@Law3514.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3515 takes them (4 nodes). -/
def ordS11R173_Law3515 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3515. -/
theorem noS11R173_Law3515 : ∀ v : Magma.tup11R173,
    ¬ @Equation3515 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3515) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3515) (by native_decide) v.1 v.2
    ((@Law3515.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3516 takes them (3 nodes). -/
def ordS11R173_Law3516 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3516. -/
theorem noS11R173_Law3516 : ∀ v : Magma.tup11R173,
    ¬ @Equation3516 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3516) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3516) (by native_decide) v.1 v.2
    ((@Law3516.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3517 takes them (3 nodes). -/
def ordS11R173_Law3517 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3517. -/
theorem noS11R173_Law3517 : ∀ v : Magma.tup11R173,
    ¬ @Equation3517 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3517) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3517) (by native_decide) v.1 v.2
    ((@Law3517.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3519 takes them (4 nodes). -/
def ordS11R173_Law3519 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3519. -/
theorem noS11R173_Law3519 : ∀ v : Magma.tup11R173,
    ¬ @Equation3519 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3519) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3519) (by native_decide) v.1 v.2
    ((@Law3519.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (3 nodes). -/
def ordS11R173_Law3520 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3520. -/
theorem noS11R173_Law3520 : ∀ v : Magma.tup11R173,
    ¬ @Equation3520 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (3 nodes). -/
def ordS11R173_Law3521 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3521. -/
theorem noS11R173_Law3521 : ∀ v : Magma.tup11R173,
    ¬ @Equation3521 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (3 nodes). -/
def ordS11R173_Law3523 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3523. -/
theorem noS11R173_Law3523 : ∀ v : Magma.tup11R173,
    ¬ @Equation3523 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (3 nodes). -/
def ordS11R173_Law3524 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3524. -/
theorem noS11R173_Law3524 : ∀ v : Magma.tup11R173,
    ¬ @Equation3524 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3525 takes them (4 nodes). -/
def ordS11R173_Law3525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3525. -/
theorem noS11R173_Law3525 : ∀ v : Magma.tup11R173,
    ¬ @Equation3525 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3525) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3525) (by native_decide) v.1 v.2
    ((@Law3525.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (3 nodes). -/
def ordS11R173_Law3527 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3527. -/
theorem noS11R173_Law3527 : ∀ v : Magma.tup11R173,
    ¬ @Equation3527 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3528 takes them (3 nodes). -/
def ordS11R173_Law3528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3528. -/
theorem noS11R173_Law3528 : ∀ v : Magma.tup11R173,
    ¬ @Equation3528 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3528) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3528) (by native_decide) v.1 v.2
    ((@Law3528.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (4 nodes). -/
def ordS11R173_Law3529 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3529. -/
theorem noS11R173_Law3529 : ∀ v : Magma.tup11R173,
    ¬ @Equation3529 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3530 takes them (3 nodes). -/
def ordS11R173_Law3530 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3530. -/
theorem noS11R173_Law3530 : ∀ v : Magma.tup11R173,
    ¬ @Equation3530 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3530) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3530) (by native_decide) v.1 v.2
    ((@Law3530.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3531 takes them (3 nodes). -/
def ordS11R173_Law3531 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3531. -/
theorem noS11R173_Law3531 : ∀ v : Magma.tup11R173,
    ¬ @Equation3531 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3531) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3531) (by native_decide) v.1 v.2
    ((@Law3531.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3532 takes them (3 nodes). -/
def ordS11R173_Law3532 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3532. -/
theorem noS11R173_Law3532 : ∀ v : Magma.tup11R173,
    ¬ @Equation3532 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3532) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3532) (by native_decide) v.1 v.2
    ((@Law3532.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3533 takes them (4 nodes). -/
def ordS11R173_Law3533 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3533. -/
theorem noS11R173_Law3533 : ∀ v : Magma.tup11R173,
    ¬ @Equation3533 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3533) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3533) (by native_decide) v.1 v.2
    ((@Law3533.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (3 nodes). -/
def ordS11R173_Law3534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3534. -/
theorem noS11R173_Law3534 : ∀ v : Magma.tup11R173,
    ¬ @Equation3534 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3535 takes them (3 nodes). -/
def ordS11R173_Law3535 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3535. -/
theorem noS11R173_Law3535 : ∀ v : Magma.tup11R173,
    ¬ @Equation3535 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3535) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3535) (by native_decide) v.1 v.2
    ((@Law3535.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3536 takes them (3 nodes). -/
def ordS11R173_Law3536 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3536. -/
theorem noS11R173_Law3536 : ∀ v : Magma.tup11R173,
    ¬ @Equation3536 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3536) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3536) (by native_decide) v.1 v.2
    ((@Law3536.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3537 takes them (4 nodes). -/
def ordS11R173_Law3537 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3537. -/
theorem noS11R173_Law3537 : ∀ v : Magma.tup11R173,
    ¬ @Equation3537 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3537) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3537) (by native_decide) v.1 v.2
    ((@Law3537.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3538 takes them (3 nodes). -/
def ordS11R173_Law3538 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3538. -/
theorem noS11R173_Law3538 : ∀ v : Magma.tup11R173,
    ¬ @Equation3538 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3538) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3538) (by native_decide) v.1 v.2
    ((@Law3538.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3539 takes them (3 nodes). -/
def ordS11R173_Law3539 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3539. -/
theorem noS11R173_Law3539 : ∀ v : Magma.tup11R173,
    ¬ @Equation3539 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3539) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3539) (by native_decide) v.1 v.2
    ((@Law3539.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3540 takes them (3 nodes). -/
def ordS11R173_Law3540 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3540. -/
theorem noS11R173_Law3540 : ∀ v : Magma.tup11R173,
    ¬ @Equation3540 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3540) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3540) (by native_decide) v.1 v.2
    ((@Law3540.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_5 :
    FamilyRefutes Magma.srch11R173 [
      3256, 3257, 3258, 3259, 3260, 3262, 3263, 3264, 3265, 3266, 3267, 3271, 3281, 3305, 3307,
      3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3320, 3321, 3322, 3323,
      3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3335, 3336, 3337, 3338, 3339,
      3340, 3346, 3388, 3457, 3458, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469,
      3470, 3474, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3519, 3520, 3521,
      3523, 3524, 3525, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538,
      3539, 3540
    ] :=
  ⟨noS11R173_Law3256, noS11R173_Law3257, noS11R173_Law3258, noS11R173_Law3259, noS11R173_Law3260, noS11R173_Law3262, noS11R173_Law3263, noS11R173_Law3264, noS11R173_Law3265, noS11R173_Law3266, noS11R173_Law3267, noS11R173_Law3271, noS11R173_Law3281, noS11R173_Law3305, noS11R173_Law3307, noS11R173_Law3308, noS11R173_Law3309, noS11R173_Law3310, noS11R173_Law3311, noS11R173_Law3312, noS11R173_Law3313, noS11R173_Law3314, noS11R173_Law3315, noS11R173_Law3316, noS11R173_Law3317, noS11R173_Law3318, noS11R173_Law3320, noS11R173_Law3321, noS11R173_Law3322, noS11R173_Law3323, noS11R173_Law3324, noS11R173_Law3325, noS11R173_Law3326, noS11R173_Law3327, noS11R173_Law3328, noS11R173_Law3329, noS11R173_Law3330, noS11R173_Law3331, noS11R173_Law3332, noS11R173_Law3333, noS11R173_Law3335, noS11R173_Law3336, noS11R173_Law3337, noS11R173_Law3338, noS11R173_Law3339, noS11R173_Law3340, noS11R173_Law3346, noS11R173_Law3388, noS11R173_Law3457, noS11R173_Law3458, noS11R173_Law3460, noS11R173_Law3461, noS11R173_Law3462, noS11R173_Law3463, noS11R173_Law3464, noS11R173_Law3465, noS11R173_Law3466, noS11R173_Law3467, noS11R173_Law3468, noS11R173_Law3469, noS11R173_Law3470, noS11R173_Law3474, noS11R173_Law3508, noS11R173_Law3509, noS11R173_Law3510, noS11R173_Law3511, noS11R173_Law3512, noS11R173_Law3513, noS11R173_Law3514, noS11R173_Law3515, noS11R173_Law3516, noS11R173_Law3517, noS11R173_Law3519, noS11R173_Law3520, noS11R173_Law3521, noS11R173_Law3523, noS11R173_Law3524, noS11R173_Law3525, noS11R173_Law3527, noS11R173_Law3528, noS11R173_Law3529, noS11R173_Law3530, noS11R173_Law3531, noS11R173_Law3532, noS11R173_Law3533, noS11R173_Law3534, noS11R173_Law3535, noS11R173_Law3536, noS11R173_Law3537, noS11R173_Law3538, noS11R173_Law3539, noS11R173_Law3540⟩

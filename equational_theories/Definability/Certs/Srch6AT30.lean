import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 31 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `33`
equations here, 2,526 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3163 takes them (141 nodes). -/
def ordS6A_Law3163 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3163. -/
theorem noS6A_Law3163 : ∀ v : Magma.tupS6A,
    ¬ @Equation3163 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3163) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3163) (by native_decide) v.1 v.2
    ((@Law3163.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3171 takes them (108 nodes). -/
def ordS6A_Law3171 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3171. -/
theorem noS6A_Law3171 : ∀ v : Magma.tupS6A,
    ¬ @Equation3171 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3171) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3171) (by native_decide) v.1 v.2
    ((@Law3171.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3184 takes them (66 nodes). -/
def ordS6A_Law3184 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3184. -/
theorem noS6A_Law3184 : ∀ v : Magma.tupS6A,
    ¬ @Equation3184 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3184) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3184) (by native_decide) v.1 v.2
    ((@Law3184.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3188 takes them (66 nodes). -/
def ordS6A_Law3188 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3188. -/
theorem noS6A_Law3188 : ∀ v : Magma.tupS6A,
    ¬ @Equation3188 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3188) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3188) (by native_decide) v.1 v.2
    ((@Law3188.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3205 takes them (67 nodes). -/
def ordS6A_Law3205 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3205. -/
theorem noS6A_Law3205 : ∀ v : Magma.tupS6A,
    ¬ @Equation3205 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3205) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3205) (by native_decide) v.1 v.2
    ((@Law3205.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3218 takes them (40 nodes). -/
def ordS6A_Law3218 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3218. -/
theorem noS6A_Law3218 : ∀ v : Magma.tupS6A,
    ¬ @Equation3218 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3218) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3218) (by native_decide) v.1 v.2
    ((@Law3218.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3222 takes them (30 nodes). -/
def ordS6A_Law3222 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3222. -/
theorem noS6A_Law3222 : ∀ v : Magma.tupS6A,
    ¬ @Equation3222 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3222) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3222) (by native_decide) v.1 v.2
    ((@Law3222.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3232 takes them (76 nodes). -/
def ordS6A_Law3232 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3232. -/
theorem noS6A_Law3232 : ∀ v : Magma.tupS6A,
    ¬ @Equation3232 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3232) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3232) (by native_decide) v.1 v.2
    ((@Law3232.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3237 takes them (26 nodes). -/
def ordS6A_Law3237 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3237. -/
theorem noS6A_Law3237 : ∀ v : Magma.tupS6A,
    ¬ @Equation3237 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3237) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3237) (by native_decide) v.1 v.2
    ((@Law3237.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3242 takes them (36 nodes). -/
def ordS6A_Law3242 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3242. -/
theorem noS6A_Law3242 : ∀ v : Magma.tupS6A,
    ¬ @Equation3242 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3242) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3242) (by native_decide) v.1 v.2
    ((@Law3242.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3247 takes them (26 nodes). -/
def ordS6A_Law3247 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3247. -/
theorem noS6A_Law3247 : ∀ v : Magma.tupS6A,
    ¬ @Equation3247 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3247) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3247) (by native_decide) v.1 v.2
    ((@Law3247.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3305 takes them (123 nodes). -/
def ordS6A_Law3305 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3305. -/
theorem noS6A_Law3305 : ∀ v : Magma.tupS6A,
    ¬ @Equation3305 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3305) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3305) (by native_decide) v.1 v.2
    ((@Law3305.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3307 takes them (59 nodes). -/
def ordS6A_Law3307 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3307. -/
theorem noS6A_Law3307 : ∀ v : Magma.tupS6A,
    ¬ @Equation3307 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3307) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3307) (by native_decide) v.1 v.2
    ((@Law3307.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3310 takes them (102 nodes). -/
def ordS6A_Law3310 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3310. -/
theorem noS6A_Law3310 : ∀ v : Magma.tupS6A,
    ¬ @Equation3310 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3310) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3310) (by native_decide) v.1 v.2
    ((@Law3310.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3311 takes them (67 nodes). -/
def ordS6A_Law3311 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3311. -/
theorem noS6A_Law3311 : ∀ v : Magma.tupS6A,
    ¬ @Equation3311 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3311) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3311) (by native_decide) v.1 v.2
    ((@Law3311.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3312 takes them (144 nodes). -/
def ordS6A_Law3312 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3312. -/
theorem noS6A_Law3312 : ∀ v : Magma.tupS6A,
    ¬ @Equation3312 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3312) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3312) (by native_decide) v.1 v.2
    ((@Law3312.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3313 takes them (67 nodes). -/
def ordS6A_Law3313 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3313. -/
theorem noS6A_Law3313 : ∀ v : Magma.tupS6A,
    ¬ @Equation3313 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3313) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3313) (by native_decide) v.1 v.2
    ((@Law3313.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3314 takes them (47 nodes). -/
def ordS6A_Law3314 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3314. -/
theorem noS6A_Law3314 : ∀ v : Magma.tupS6A,
    ¬ @Equation3314 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3314) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3314) (by native_decide) v.1 v.2
    ((@Law3314.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3325 takes them (77 nodes). -/
def ordS6A_Law3325 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3325. -/
theorem noS6A_Law3325 : ∀ v : Magma.tupS6A,
    ¬ @Equation3325 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3325) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3325) (by native_decide) v.1 v.2
    ((@Law3325.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3327 takes them (43 nodes). -/
def ordS6A_Law3327 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3327. -/
theorem noS6A_Law3327 : ∀ v : Magma.tupS6A,
    ¬ @Equation3327 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3327) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3327) (by native_decide) v.1 v.2
    ((@Law3327.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3328 takes them (39 nodes). -/
def ordS6A_Law3328 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3328. -/
theorem noS6A_Law3328 : ∀ v : Magma.tupS6A,
    ¬ @Equation3328 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3328) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3328) (by native_decide) v.1 v.2
    ((@Law3328.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3329 takes them (150 nodes). -/
def ordS6A_Law3329 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3329. -/
theorem noS6A_Law3329 : ∀ v : Magma.tupS6A,
    ¬ @Equation3329 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3329) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3329) (by native_decide) v.1 v.2
    ((@Law3329.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3330 takes them (397 nodes). -/
def ordS6A_Law3330 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3330. -/
theorem noS6A_Law3330 : ∀ v : Magma.tupS6A,
    ¬ @Equation3330 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3330) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3330) (by native_decide) v.1 v.2
    ((@Law3330.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3332 takes them (70 nodes). -/
def ordS6A_Law3332 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3332. -/
theorem noS6A_Law3332 : ∀ v : Magma.tupS6A,
    ¬ @Equation3332 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3332) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3332) (by native_decide) v.1 v.2
    ((@Law3332.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3333 takes them (43 nodes). -/
def ordS6A_Law3333 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3333. -/
theorem noS6A_Law3333 : ∀ v : Magma.tupS6A,
    ¬ @Equation3333 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3333) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3333) (by native_decide) v.1 v.2
    ((@Law3333.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3335 takes them (43 nodes). -/
def ordS6A_Law3335 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3335. -/
theorem noS6A_Law3335 : ∀ v : Magma.tupS6A,
    ¬ @Equation3335 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3335) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3335) (by native_decide) v.1 v.2
    ((@Law3335.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3336 takes them (39 nodes). -/
def ordS6A_Law3336 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3336. -/
theorem noS6A_Law3336 : ∀ v : Magma.tupS6A,
    ¬ @Equation3336 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3336) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3336) (by native_decide) v.1 v.2
    ((@Law3336.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3337 takes them (43 nodes). -/
def ordS6A_Law3337 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3337. -/
theorem noS6A_Law3337 : ∀ v : Magma.tupS6A,
    ¬ @Equation3337 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3337) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3337) (by native_decide) v.1 v.2
    ((@Law3337.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3338 takes them (126 nodes). -/
def ordS6A_Law3338 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3338. -/
theorem noS6A_Law3338 : ∀ v : Magma.tupS6A,
    ¬ @Equation3338 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3338) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3338) (by native_decide) v.1 v.2
    ((@Law3338.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3339 takes them (43 nodes). -/
def ordS6A_Law3339 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3339. -/
theorem noS6A_Law3339 : ∀ v : Magma.tupS6A,
    ¬ @Equation3339 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3339) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3339) (by native_decide) v.1 v.2
    ((@Law3339.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3340 takes them (43 nodes). -/
def ordS6A_Law3340 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3340. -/
theorem noS6A_Law3340 : ∀ v : Magma.tupS6A,
    ¬ @Equation3340 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3340) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3340) (by native_decide) v.1 v.2
    ((@Law3340.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3341 takes them (39 nodes). -/
def ordS6A_Law3341 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3341. -/
theorem noS6A_Law3341 : ∀ v : Magma.tupS6A,
    ¬ @Equation3341 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3341) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3341) (by native_decide) v.1 v.2
    ((@Law3341.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3344 takes them (40 nodes). -/
def ordS6A_Law3344 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3344. -/
theorem noS6A_Law3344 : ∀ v : Magma.tupS6A,
    ¬ @Equation3344 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3344) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3344) (by native_decide) v.1 v.2
    ((@Law3344.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `33` equations. -/
theorem srch6A_refutes_30 :
    FamilyRefutes Magma.srch6A [
      3163, 3171, 3184, 3188, 3205, 3218, 3222, 3232, 3237, 3242, 3247, 3305, 3307, 3310, 3311,
      3312, 3313, 3314, 3325, 3327, 3328, 3329, 3330, 3332, 3333, 3335, 3336, 3337, 3338, 3339,
      3340, 3341, 3344
    ] :=
  ⟨noS6A_Law3163, noS6A_Law3171, noS6A_Law3184, noS6A_Law3188, noS6A_Law3205, noS6A_Law3218, noS6A_Law3222, noS6A_Law3232, noS6A_Law3237, noS6A_Law3242, noS6A_Law3247, noS6A_Law3305, noS6A_Law3307, noS6A_Law3310, noS6A_Law3311, noS6A_Law3312, noS6A_Law3313, noS6A_Law3314, noS6A_Law3325, noS6A_Law3327, noS6A_Law3328, noS6A_Law3329, noS6A_Law3330, noS6A_Law3332, noS6A_Law3333, noS6A_Law3335, noS6A_Law3336, noS6A_Law3337, noS6A_Law3338, noS6A_Law3339, noS6A_Law3340, noS6A_Law3341, noS6A_Law3344⟩

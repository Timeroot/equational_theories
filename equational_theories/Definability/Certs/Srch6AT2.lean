import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 3 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `33`
equations here, 2,562 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 234 takes them (34 nodes). -/
def ordS6A_Law234 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 234. -/
theorem noS6A_Law234 : ∀ v : Magma.tupS6A,
    ¬ @Equation234 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law234) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law234) (by native_decide) v.1 v.2
    ((@Law234.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 250 takes them (29 nodes). -/
def ordS6A_Law250 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 250. -/
theorem noS6A_Law250 : ∀ v : Magma.tupS6A,
    ¬ @Equation250 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law250) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law250) (by native_decide) v.1 v.2
    ((@Law250.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 256 takes them (140 nodes). -/
def ordS6A_Law256 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 256. -/
theorem noS6A_Law256 : ∀ v : Magma.tupS6A,
    ¬ @Equation256 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law256) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law256) (by native_decide) v.1 v.2
    ((@Law256.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 259 takes them (122 nodes). -/
def ordS6A_Law259 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 259. -/
theorem noS6A_Law259 : ∀ v : Magma.tupS6A,
    ¬ @Equation259 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law259) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law259) (by native_decide) v.1 v.2
    ((@Law259.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 261 takes them (278 nodes). -/
def ordS6A_Law261 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 261. -/
theorem noS6A_Law261 : ∀ v : Magma.tupS6A,
    ¬ @Equation261 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law261) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law261) (by native_decide) v.1 v.2
    ((@Law261.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 262 takes them (72 nodes). -/
def ordS6A_Law262 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 262. -/
theorem noS6A_Law262 : ∀ v : Magma.tupS6A,
    ¬ @Equation262 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law262) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law262) (by native_decide) v.1 v.2
    ((@Law262.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 265 takes them (30 nodes). -/
def ordS6A_Law265 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 265. -/
theorem noS6A_Law265 : ∀ v : Magma.tupS6A,
    ¬ @Equation265 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law265) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law265) (by native_decide) v.1 v.2
    ((@Law265.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 267 takes them (136 nodes). -/
def ordS6A_Law267 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 267. -/
theorem noS6A_Law267 : ∀ v : Magma.tupS6A,
    ¬ @Equation267 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law267) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law267) (by native_decide) v.1 v.2
    ((@Law267.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 268 takes them (136 nodes). -/
def ordS6A_Law268 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 268. -/
theorem noS6A_Law268 : ∀ v : Magma.tupS6A,
    ¬ @Equation268 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law268) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law268) (by native_decide) v.1 v.2
    ((@Law268.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 269 takes them (26 nodes). -/
def ordS6A_Law269 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 269. -/
theorem noS6A_Law269 : ∀ v : Magma.tupS6A,
    ¬ @Equation269 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law269) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law269) (by native_decide) v.1 v.2
    ((@Law269.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 276 takes them (66 nodes). -/
def ordS6A_Law276 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 276. -/
theorem noS6A_Law276 : ∀ v : Magma.tupS6A,
    ¬ @Equation276 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law276) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law276) (by native_decide) v.1 v.2
    ((@Law276.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 286 takes them (99 nodes). -/
def ordS6A_Law286 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 286. -/
theorem noS6A_Law286 : ∀ v : Magma.tupS6A,
    ¬ @Equation286 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law286) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law286) (by native_decide) v.1 v.2
    ((@Law286.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 294 takes them (67 nodes). -/
def ordS6A_Law294 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 294. -/
theorem noS6A_Law294 : ∀ v : Magma.tupS6A,
    ¬ @Equation294 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law294) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law294) (by native_decide) v.1 v.2
    ((@Law294.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 298 takes them (36 nodes). -/
def ordS6A_Law298 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 298. -/
theorem noS6A_Law298 : ∀ v : Magma.tupS6A,
    ¬ @Equation298 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law298) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law298) (by native_decide) v.1 v.2
    ((@Law298.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 302 takes them (26 nodes). -/
def ordS6A_Law302 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 302. -/
theorem noS6A_Law302 : ∀ v : Magma.tupS6A,
    ¬ @Equation302 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law302) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law302) (by native_decide) v.1 v.2
    ((@Law302.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 322 takes them (111 nodes). -/
def ordS6A_Law322 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 322. -/
theorem noS6A_Law322 : ∀ v : Magma.tupS6A,
    ¬ @Equation322 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law322) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law322) (by native_decide) v.1 v.2
    ((@Law322.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 324 takes them (43 nodes). -/
def ordS6A_Law324 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 324. -/
theorem noS6A_Law324 : ∀ v : Magma.tupS6A,
    ¬ @Equation324 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law324) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law324) (by native_decide) v.1 v.2
    ((@Law324.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 328 takes them (43 nodes). -/
def ordS6A_Law328 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 328. -/
theorem noS6A_Law328 : ∀ v : Magma.tupS6A,
    ¬ @Equation328 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law328) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law328) (by native_decide) v.1 v.2
    ((@Law328.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 329 takes them (89 nodes). -/
def ordS6A_Law329 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 329. -/
theorem noS6A_Law329 : ∀ v : Magma.tupS6A,
    ¬ @Equation329 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law329) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law329) (by native_decide) v.1 v.2
    ((@Law329.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 330 takes them (43 nodes). -/
def ordS6A_Law330 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 330. -/
theorem noS6A_Law330 : ∀ v : Magma.tupS6A,
    ¬ @Equation330 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law330) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law330) (by native_decide) v.1 v.2
    ((@Law330.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 331 takes them (39 nodes). -/
def ordS6A_Law331 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 331. -/
theorem noS6A_Law331 : ∀ v : Magma.tupS6A,
    ¬ @Equation331 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law331) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law331) (by native_decide) v.1 v.2
    ((@Law331.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 334 takes them (26 nodes). -/
def ordS6A_Law334 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 334. -/
theorem noS6A_Law334 : ∀ v : Magma.tupS6A,
    ¬ @Equation334 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law334) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law334) (by native_decide) v.1 v.2
    ((@Law334.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 335 takes them (250 nodes). -/
def ordS6A_Law335 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 335. -/
theorem noS6A_Law335 : ∀ v : Magma.tupS6A,
    ¬ @Equation335 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law335) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law335) (by native_decide) v.1 v.2
    ((@Law335.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 336 takes them (209 nodes). -/
def ordS6A_Law336 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 336. -/
theorem noS6A_Law336 : ∀ v : Magma.tupS6A,
    ¬ @Equation336 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law336) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law336) (by native_decide) v.1 v.2
    ((@Law336.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 337 takes them (29 nodes). -/
def ordS6A_Law337 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 337. -/
theorem noS6A_Law337 : ∀ v : Magma.tupS6A,
    ¬ @Equation337 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law337) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law337) (by native_decide) v.1 v.2
    ((@Law337.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 338 takes them (52 nodes). -/
def ordS6A_Law338 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 338. -/
theorem noS6A_Law338 : ∀ v : Magma.tupS6A,
    ¬ @Equation338 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law338) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law338) (by native_decide) v.1 v.2
    ((@Law338.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 339 takes them (125 nodes). -/
def ordS6A_Law339 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 339. -/
theorem noS6A_Law339 : ∀ v : Magma.tupS6A,
    ¬ @Equation339 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law339) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law339) (by native_decide) v.1 v.2
    ((@Law339.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 340 takes them (64 nodes). -/
def ordS6A_Law340 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 340. -/
theorem noS6A_Law340 : ∀ v : Magma.tupS6A,
    ¬ @Equation340 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law340) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law340) (by native_decide) v.1 v.2
    ((@Law340.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 341 takes them (26 nodes). -/
def ordS6A_Law341 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 341. -/
theorem noS6A_Law341 : ∀ v : Magma.tupS6A,
    ¬ @Equation341 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law341) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law341) (by native_decide) v.1 v.2
    ((@Law341.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 342 takes them (25 nodes). -/
def ordS6A_Law342 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 342. -/
theorem noS6A_Law342 : ∀ v : Magma.tupS6A,
    ¬ @Equation342 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law342) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law342) (by native_decide) v.1 v.2
    ((@Law342.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 344 takes them (14 nodes). -/
def ordS6A_Law344 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 344. -/
theorem noS6A_Law344 : ∀ v : Magma.tupS6A,
    ¬ @Equation344 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law344) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law344) (by native_decide) v.1 v.2
    ((@Law344.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 345 takes them (14 nodes). -/
def ordS6A_Law345 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 345. -/
theorem noS6A_Law345 : ∀ v : Magma.tupS6A,
    ¬ @Equation345 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law345) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law345) (by native_decide) v.1 v.2
    ((@Law345.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 346 takes them (63 nodes). -/
def ordS6A_Law346 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 346. -/
theorem noS6A_Law346 : ∀ v : Magma.tupS6A,
    ¬ @Equation346 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law346) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law346) (by native_decide) v.1 v.2
    ((@Law346.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `33` equations. -/
theorem srch6A_refutes_2 :
    FamilyRefutes Magma.srch6A [
      234, 250, 256, 259, 261, 262, 265, 267, 268, 269, 276, 286, 294, 298, 302, 322, 324, 328,
      329, 330, 331, 334, 335, 336, 337, 338, 339, 340, 341, 342, 344, 345, 346
    ] :=
  ⟨noS6A_Law234, noS6A_Law250, noS6A_Law256, noS6A_Law259, noS6A_Law261, noS6A_Law262, noS6A_Law265, noS6A_Law267, noS6A_Law268, noS6A_Law269, noS6A_Law276, noS6A_Law286, noS6A_Law294, noS6A_Law298, noS6A_Law302, noS6A_Law322, noS6A_Law324, noS6A_Law328, noS6A_Law329, noS6A_Law330, noS6A_Law331, noS6A_Law334, noS6A_Law335, noS6A_Law336, noS6A_Law337, noS6A_Law338, noS6A_Law339, noS6A_Law340, noS6A_Law341, noS6A_Law342, noS6A_Law344, noS6A_Law345, noS6A_Law346⟩

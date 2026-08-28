import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 11 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `25`
equations here, 2,928 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1202 takes them (59 nodes). -/
def ordS6A_Law1202 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1202. -/
theorem noS6A_Law1202 : ∀ v : Magma.tupS6A,
    ¬ @Equation1202 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1202) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1202) (by native_decide) v.1 v.2
    ((@Law1202.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1207 takes them (44 nodes). -/
def ordS6A_Law1207 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1207. -/
theorem noS6A_Law1207 : ∀ v : Magma.tupS6A,
    ¬ @Equation1207 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1207) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1207) (by native_decide) v.1 v.2
    ((@Law1207.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1212 takes them (64 nodes). -/
def ordS6A_Law1212 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1212. -/
theorem noS6A_Law1212 : ∀ v : Magma.tupS6A,
    ¬ @Equation1212 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1212) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1212) (by native_decide) v.1 v.2
    ((@Law1212.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1217 takes them (37 nodes). -/
def ordS6A_Law1217 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1217. -/
theorem noS6A_Law1217 : ∀ v : Magma.tupS6A,
    ¬ @Equation1217 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1217) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1217) (by native_decide) v.1 v.2
    ((@Law1217.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1268 takes them (70 nodes). -/
def ordS6A_Law1268 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1268. -/
theorem noS6A_Law1268 : ∀ v : Magma.tupS6A,
    ¬ @Equation1268 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1268) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1268) (by native_decide) v.1 v.2
    ((@Law1268.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1269 takes them (42 nodes). -/
def ordS6A_Law1269 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1269. -/
theorem noS6A_Law1269 : ∀ v : Magma.tupS6A,
    ¬ @Equation1269 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1269) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1269) (by native_decide) v.1 v.2
    ((@Law1269.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1272 takes them (64 nodes). -/
def ordS6A_Law1272 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1272. -/
theorem noS6A_Law1272 : ∀ v : Magma.tupS6A,
    ¬ @Equation1272 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1272) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1272) (by native_decide) v.1 v.2
    ((@Law1272.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1273 takes them (64 nodes). -/
def ordS6A_Law1273 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1273. -/
theorem noS6A_Law1273 : ∀ v : Magma.tupS6A,
    ¬ @Equation1273 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1273) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1273) (by native_decide) v.1 v.2
    ((@Law1273.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1274 takes them (38 nodes). -/
def ordS6A_Law1274 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1274. -/
theorem noS6A_Law1274 : ∀ v : Magma.tupS6A,
    ¬ @Equation1274 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1274) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1274) (by native_decide) v.1 v.2
    ((@Law1274.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1275 takes them (204 nodes). -/
def ordS6A_Law1275 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1275. -/
theorem noS6A_Law1275 : ∀ v : Magma.tupS6A,
    ¬ @Equation1275 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1275) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1275) (by native_decide) v.1 v.2
    ((@Law1275.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1281 takes them (181 nodes). -/
def ordS6A_Law1281 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1281. -/
theorem noS6A_Law1281 : ∀ v : Magma.tupS6A,
    ¬ @Equation1281 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1281) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1281) (by native_decide) v.1 v.2
    ((@Law1281.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1291 takes them (163 nodes). -/
def ordS6A_Law1291 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1291. -/
theorem noS6A_Law1291 : ∀ v : Magma.tupS6A,
    ¬ @Equation1291 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1291) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1291) (by native_decide) v.1 v.2
    ((@Law1291.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1295 takes them (118 nodes). -/
def ordS6A_Law1295 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1295. -/
theorem noS6A_Law1295 : ∀ v : Magma.tupS6A,
    ¬ @Equation1295 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1295) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1295) (by native_decide) v.1 v.2
    ((@Law1295.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1303 takes them (74 nodes). -/
def ordS6A_Law1303 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1303. -/
theorem noS6A_Law1303 : ∀ v : Magma.tupS6A,
    ¬ @Equation1303 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1303) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1303) (by native_decide) v.1 v.2
    ((@Law1303.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1307 takes them (70 nodes). -/
def ordS6A_Law1307 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1307. -/
theorem noS6A_Law1307 : ∀ v : Magma.tupS6A,
    ¬ @Equation1307 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1307) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1307) (by native_decide) v.1 v.2
    ((@Law1307.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (739 nodes). -/
def ordS6A_Law1312 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1312. -/
theorem noS6A_Law1312 : ∀ v : Magma.tupS6A,
    ¬ @Equation1312 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1318 takes them (89 nodes). -/
def ordS6A_Law1318 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1318. -/
theorem noS6A_Law1318 : ∀ v : Magma.tupS6A,
    ¬ @Equation1318 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1318) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1318) (by native_decide) v.1 v.2
    ((@Law1318.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1322 takes them (291 nodes). -/
def ordS6A_Law1322 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1322. -/
theorem noS6A_Law1322 : ∀ v : Magma.tupS6A,
    ¬ @Equation1322 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1322) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1322) (by native_decide) v.1 v.2
    ((@Law1322.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1328 takes them (109 nodes). -/
def ordS6A_Law1328 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1328. -/
theorem noS6A_Law1328 : ∀ v : Magma.tupS6A,
    ¬ @Equation1328 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1328) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1328) (by native_decide) v.1 v.2
    ((@Law1328.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1332 takes them (69 nodes). -/
def ordS6A_Law1332 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1332. -/
theorem noS6A_Law1332 : ∀ v : Magma.tupS6A,
    ¬ @Equation1332 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1332) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1332) (by native_decide) v.1 v.2
    ((@Law1332.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1340 takes them (116 nodes). -/
def ordS6A_Law1340 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1340. -/
theorem noS6A_Law1340 : ∀ v : Magma.tupS6A,
    ¬ @Equation1340 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1340) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1340) (by native_decide) v.1 v.2
    ((@Law1340.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1344 takes them (39 nodes). -/
def ordS6A_Law1344 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1344. -/
theorem noS6A_Law1344 : ∀ v : Magma.tupS6A,
    ¬ @Equation1344 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1344) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1344) (by native_decide) v.1 v.2
    ((@Law1344.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1349 takes them (64 nodes). -/
def ordS6A_Law1349 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1349. -/
theorem noS6A_Law1349 : ∀ v : Magma.tupS6A,
    ¬ @Equation1349 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1349) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1349) (by native_decide) v.1 v.2
    ((@Law1349.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1357 takes them (78 nodes). -/
def ordS6A_Law1357 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1357. -/
theorem noS6A_Law1357 : ∀ v : Magma.tupS6A,
    ¬ @Equation1357 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1357) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1357) (by native_decide) v.1 v.2
    ((@Law1357.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1361 takes them (42 nodes). -/
def ordS6A_Law1361 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1361. -/
theorem noS6A_Law1361 : ∀ v : Magma.tupS6A,
    ¬ @Equation1361 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1361) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1361) (by native_decide) v.1 v.2
    ((@Law1361.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch6A_refutes_10 :
    FamilyRefutes Magma.srch6A [
      1202, 1207, 1212, 1217, 1268, 1269, 1272, 1273, 1274, 1275, 1281, 1291, 1295, 1303, 1307,
      1312, 1318, 1322, 1328, 1332, 1340, 1344, 1349, 1357, 1361
    ] :=
  ⟨noS6A_Law1202, noS6A_Law1207, noS6A_Law1212, noS6A_Law1217, noS6A_Law1268, noS6A_Law1269, noS6A_Law1272, noS6A_Law1273, noS6A_Law1274, noS6A_Law1275, noS6A_Law1281, noS6A_Law1291, noS6A_Law1295, noS6A_Law1303, noS6A_Law1307, noS6A_Law1312, noS6A_Law1318, noS6A_Law1322, noS6A_Law1328, noS6A_Law1332, noS6A_Law1340, noS6A_Law1344, noS6A_Law1349, noS6A_Law1357, noS6A_Law1361⟩

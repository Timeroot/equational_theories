import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 4 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 299 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2079 takes them (3 nodes). -/
def ordS8R130_Law2079 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2079. -/
theorem noS8R130_Law2079 : ∀ v : Magma.tup8R130,
    ¬ @Equation2079 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2079) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2079) (by native_decide) v.1 v.2
    ((@Law2079.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2087 takes them (3 nodes). -/
def ordS8R130_Law2087 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2087. -/
theorem noS8R130_Law2087 : ∀ v : Magma.tup8R130,
    ¬ @Equation2087 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2087) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2087) (by native_decide) v.1 v.2
    ((@Law2087.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (3 nodes). -/
def ordS8R130_Law2090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2090. -/
theorem noS8R130_Law2090 : ∀ v : Magma.tup8R130,
    ¬ @Equation2090 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2097 takes them (3 nodes). -/
def ordS8R130_Law2097 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2097. -/
theorem noS8R130_Law2097 : ∀ v : Magma.tup8R130,
    ¬ @Equation2097 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2097) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2097) (by native_decide) v.1 v.2
    ((@Law2097.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2124 takes them (3 nodes). -/
def ordS8R130_Law2124 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2124. -/
theorem noS8R130_Law2124 : ∀ v : Magma.tup8R130,
    ¬ @Equation2124 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2124) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2124) (by native_decide) v.1 v.2
    ((@Law2124.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (3 nodes). -/
def ordS8R130_Law2137 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2137. -/
theorem noS8R130_Law2137 : ∀ v : Magma.tup8R130,
    ¬ @Equation2137 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2152 takes them (3 nodes). -/
def ordS8R130_Law2152 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2152. -/
theorem noS8R130_Law2152 : ∀ v : Magma.tup8R130,
    ¬ @Equation2152 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2152) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2152) (by native_decide) v.1 v.2
    ((@Law2152.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2161 takes them (3 nodes). -/
def ordS8R130_Law2161 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2161. -/
theorem noS8R130_Law2161 : ∀ v : Magma.tup8R130,
    ¬ @Equation2161 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2161) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2161) (by native_decide) v.1 v.2
    ((@Law2161.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (3 nodes). -/
def ordS8R130_Law2186 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2186. -/
theorem noS8R130_Law2186 : ∀ v : Magma.tup8R130,
    ¬ @Equation2186 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (3 nodes). -/
def ordS8R130_Law2199 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2199. -/
theorem noS8R130_Law2199 : ∀ v : Magma.tup8R130,
    ¬ @Equation2199 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2240 takes them (4 nodes). -/
def ordS8R130_Law2240 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2240. -/
theorem noS8R130_Law2240 : ∀ v : Magma.tup8R130,
    ¬ @Equation2240 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2240) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2240) (by native_decide) v.1 v.2
    ((@Law2240.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2243 takes them (4 nodes). -/
def ordS8R130_Law2243 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2243. -/
theorem noS8R130_Law2243 : ∀ v : Magma.tup8R130,
    ¬ @Equation2243 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2243) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2243) (by native_decide) v.1 v.2
    ((@Law2243.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2246 takes them (4 nodes). -/
def ordS8R130_Law2246 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2246. -/
theorem noS8R130_Law2246 : ∀ v : Magma.tup8R130,
    ¬ @Equation2246 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2246) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2246) (by native_decide) v.1 v.2
    ((@Law2246.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2249 takes them (4 nodes). -/
def ordS8R130_Law2249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2249. -/
theorem noS8R130_Law2249 : ∀ v : Magma.tup8R130,
    ¬ @Equation2249 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2249) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2249) (by native_decide) v.1 v.2
    ((@Law2249.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2253 takes them (4 nodes). -/
def ordS8R130_Law2253 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2253. -/
theorem noS8R130_Law2253 : ∀ v : Magma.tup8R130,
    ¬ @Equation2253 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2253) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2253) (by native_decide) v.1 v.2
    ((@Law2253.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (3 nodes). -/
def ordS8R130_Law2254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2254. -/
theorem noS8R130_Law2254 : ∀ v : Magma.tup8R130,
    ¬ @Equation2254 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2256 takes them (4 nodes). -/
def ordS8R130_Law2256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2256. -/
theorem noS8R130_Law2256 : ∀ v : Magma.tup8R130,
    ¬ @Equation2256 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2256) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2256) (by native_decide) v.1 v.2
    ((@Law2256.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (4 nodes). -/
def ordS8R130_Law2263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2263. -/
theorem noS8R130_Law2263 : ∀ v : Magma.tup8R130,
    ¬ @Equation2263 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2266 takes them (4 nodes). -/
def ordS8R130_Law2266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2266. -/
theorem noS8R130_Law2266 : ∀ v : Magma.tup8R130,
    ¬ @Equation2266 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2266) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2266) (by native_decide) v.1 v.2
    ((@Law2266.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (3 nodes). -/
def ordS8R130_Law2267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2267. -/
theorem noS8R130_Law2267 : ∀ v : Magma.tup8R130,
    ¬ @Equation2267 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2271 takes them (3 nodes). -/
def ordS8R130_Law2271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2271. -/
theorem noS8R130_Law2271 : ∀ v : Magma.tup8R130,
    ¬ @Equation2271 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2271) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2271) (by native_decide) v.1 v.2
    ((@Law2271.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (3 nodes). -/
def ordS8R130_Law2279 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2279. -/
theorem noS8R130_Law2279 : ∀ v : Magma.tup8R130,
    ¬ @Equation2279 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2281 takes them (4 nodes). -/
def ordS8R130_Law2281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2281. -/
theorem noS8R130_Law2281 : ∀ v : Magma.tup8R130,
    ¬ @Equation2281 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2281) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2281) (by native_decide) v.1 v.2
    ((@Law2281.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2282 takes them (3 nodes). -/
def ordS8R130_Law2282 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2282. -/
theorem noS8R130_Law2282 : ∀ v : Magma.tup8R130,
    ¬ @Equation2282 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2282) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2282) (by native_decide) v.1 v.2
    ((@Law2282.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2290 takes them (3 nodes). -/
def ordS8R130_Law2290 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2290. -/
theorem noS8R130_Law2290 : ∀ v : Magma.tup8R130,
    ¬ @Equation2290 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2290) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2290) (by native_decide) v.1 v.2
    ((@Law2290.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (3 nodes). -/
def ordS8R130_Law2300 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2300. -/
theorem noS8R130_Law2300 : ∀ v : Magma.tup8R130,
    ¬ @Equation2300 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (3 nodes). -/
def ordS8R130_Law2303 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2303. -/
theorem noS8R130_Law2303 : ∀ v : Magma.tup8R130,
    ¬ @Equation2303 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2318 takes them (3 nodes). -/
def ordS8R130_Law2318 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2318. -/
theorem noS8R130_Law2318 : ∀ v : Magma.tup8R130,
    ¬ @Equation2318 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2318) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2318) (by native_decide) v.1 v.2
    ((@Law2318.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (3 nodes). -/
def ordS8R130_Law2327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2327. -/
theorem noS8R130_Law2327 : ∀ v : Magma.tup8R130,
    ¬ @Equation2327 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2337 takes them (3 nodes). -/
def ordS8R130_Law2337 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2337. -/
theorem noS8R130_Law2337 : ∀ v : Magma.tup8R130,
    ¬ @Equation2337 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2337) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2337) (by native_decide) v.1 v.2
    ((@Law2337.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2340 takes them (3 nodes). -/
def ordS8R130_Law2340 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2340. -/
theorem noS8R130_Law2340 : ∀ v : Magma.tup8R130,
    ¬ @Equation2340 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2340) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2340) (by native_decide) v.1 v.2
    ((@Law2340.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2355 takes them (3 nodes). -/
def ordS8R130_Law2355 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2355. -/
theorem noS8R130_Law2355 : ∀ v : Magma.tup8R130,
    ¬ @Equation2355 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2355) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2355) (by native_decide) v.1 v.2
    ((@Law2355.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2364 takes them (3 nodes). -/
def ordS8R130_Law2364 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2364. -/
theorem noS8R130_Law2364 : ∀ v : Magma.tup8R130,
    ¬ @Equation2364 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2364) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2364) (by native_decide) v.1 v.2
    ((@Law2364.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2385 takes them (3 nodes). -/
def ordS8R130_Law2385 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2385. -/
theorem noS8R130_Law2385 : ∀ v : Magma.tup8R130,
    ¬ @Equation2385 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2385) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2385) (by native_decide) v.1 v.2
    ((@Law2385.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2389 takes them (3 nodes). -/
def ordS8R130_Law2389 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2389. -/
theorem noS8R130_Law2389 : ∀ v : Magma.tup8R130,
    ¬ @Equation2389 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2389) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2389) (by native_decide) v.1 v.2
    ((@Law2389.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2402 takes them (3 nodes). -/
def ordS8R130_Law2402 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2402. -/
theorem noS8R130_Law2402 : ∀ v : Magma.tup8R130,
    ¬ @Equation2402 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2402) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2402) (by native_decide) v.1 v.2
    ((@Law2402.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2406 takes them (3 nodes). -/
def ordS8R130_Law2406 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2406. -/
theorem noS8R130_Law2406 : ∀ v : Magma.tup8R130,
    ¬ @Equation2406 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2406) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2406) (by native_decide) v.1 v.2
    ((@Law2406.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2430 takes them (3 nodes). -/
def ordS8R130_Law2430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2430. -/
theorem noS8R130_Law2430 : ∀ v : Magma.tup8R130,
    ¬ @Equation2430 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2430) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law2430) (by native_decide) v.1 v.2
    ((@Law2430.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2443 takes them (4 nodes). -/
def ordS8R130_Law2443 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2443. -/
theorem noS8R130_Law2443 : ∀ v : Magma.tup8R130,
    ¬ @Equation2443 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2443) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2443) (by native_decide) v.1 v.2
    ((@Law2443.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (3 nodes). -/
def ordS8R130_Law2444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2444. -/
theorem noS8R130_Law2444 : ∀ v : Magma.tup8R130,
    ¬ @Equation2444 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2446 takes them (4 nodes). -/
def ordS8R130_Law2446 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2446. -/
theorem noS8R130_Law2446 : ∀ v : Magma.tup8R130,
    ¬ @Equation2446 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (4 nodes). -/
def ordS8R130_Law2449 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2449. -/
theorem noS8R130_Law2449 : ∀ v : Magma.tup8R130,
    ¬ @Equation2449 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2456 takes them (4 nodes). -/
def ordS8R130_Law2456 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2456. -/
theorem noS8R130_Law2456 : ∀ v : Magma.tup8R130,
    ¬ @Equation2456 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2456) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2456) (by native_decide) v.1 v.2
    ((@Law2456.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (3 nodes). -/
def ordS8R130_Law2457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R130_Law2457 : ∀ v : Magma.tup8R130,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2459 takes them (4 nodes). -/
def ordS8R130_Law2459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2459. -/
theorem noS8R130_Law2459 : ∀ v : Magma.tup8R130,
    ¬ @Equation2459 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2459) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2459) (by native_decide) v.1 v.2
    ((@Law2459.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2466 takes them (4 nodes). -/
def ordS8R130_Law2466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2466. -/
theorem noS8R130_Law2466 : ∀ v : Magma.tup8R130,
    ¬ @Equation2466 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2466) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2466) (by native_decide) v.1 v.2
    ((@Law2466.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (3 nodes). -/
def ordS8R130_Law2470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2470. -/
theorem noS8R130_Law2470 : ∀ v : Magma.tup8R130,
    ¬ @Equation2470 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2474 takes them (3 nodes). -/
def ordS8R130_Law2474 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2474. -/
theorem noS8R130_Law2474 : ∀ v : Magma.tup8R130,
    ¬ @Equation2474 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2474) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2474) (by native_decide) v.1 v.2
    ((@Law2474.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2476 takes them (4 nodes). -/
def ordS8R130_Law2476 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2476. -/
theorem noS8R130_Law2476 : ∀ v : Magma.tup8R130,
    ¬ @Equation2476 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2482 takes them (3 nodes). -/
def ordS8R130_Law2482 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2482. -/
theorem noS8R130_Law2482 : ∀ v : Magma.tup8R130,
    ¬ @Equation2482 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2482) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2482) (by native_decide) v.1 v.2
    ((@Law2482.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (3 nodes). -/
def ordS8R130_Law2485 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2485. -/
theorem noS8R130_Law2485 : ∀ v : Magma.tup8R130,
    ¬ @Equation2485 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2493 takes them (3 nodes). -/
def ordS8R130_Law2493 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2493. -/
theorem noS8R130_Law2493 : ∀ v : Magma.tup8R130,
    ¬ @Equation2493 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2493) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2493) (by native_decide) v.1 v.2
    ((@Law2493.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (3 nodes). -/
def ordS8R130_Law2496 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2496. -/
theorem noS8R130_Law2496 : ∀ v : Magma.tup8R130,
    ¬ @Equation2496 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2503 takes them (3 nodes). -/
def ordS8R130_Law2503 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2503. -/
theorem noS8R130_Law2503 : ∀ v : Magma.tup8R130,
    ¬ @Equation2503 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2503) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2503) (by native_decide) v.1 v.2
    ((@Law2503.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (3 nodes). -/
def ordS8R130_Law2530 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2530. -/
theorem noS8R130_Law2530 : ∀ v : Magma.tup8R130,
    ¬ @Equation2530 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2540 takes them (3 nodes). -/
def ordS8R130_Law2540 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2540. -/
theorem noS8R130_Law2540 : ∀ v : Magma.tup8R130,
    ¬ @Equation2540 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2540) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2540) (by native_decide) v.1 v.2
    ((@Law2540.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2543 takes them (3 nodes). -/
def ordS8R130_Law2543 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2543. -/
theorem noS8R130_Law2543 : ∀ v : Magma.tup8R130,
    ¬ @Equation2543 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2543) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2543) (by native_decide) v.1 v.2
    ((@Law2543.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2558 takes them (3 nodes). -/
def ordS8R130_Law2558 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2558. -/
theorem noS8R130_Law2558 : ∀ v : Magma.tup8R130,
    ¬ @Equation2558 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2558) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2558) (by native_decide) v.1 v.2
    ((@Law2558.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2567 takes them (3 nodes). -/
def ordS8R130_Law2567 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2567. -/
theorem noS8R130_Law2567 : ∀ v : Magma.tup8R130,
    ¬ @Equation2567 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2567) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2567) (by native_decide) v.1 v.2
    ((@Law2567.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2592 takes them (3 nodes). -/
def ordS8R130_Law2592 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2592. -/
theorem noS8R130_Law2592 : ∀ v : Magma.tup8R130,
    ¬ @Equation2592 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2592) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2592) (by native_decide) v.1 v.2
    ((@Law2592.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2605 takes them (3 nodes). -/
def ordS8R130_Law2605 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2605. -/
theorem noS8R130_Law2605 : ∀ v : Magma.tup8R130,
    ¬ @Equation2605 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2605) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2605) (by native_decide) v.1 v.2
    ((@Law2605.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2646 takes them (4 nodes). -/
def ordS8R130_Law2646 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2646. -/
theorem noS8R130_Law2646 : ∀ v : Magma.tup8R130,
    ¬ @Equation2646 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2646) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2646) (by native_decide) v.1 v.2
    ((@Law2646.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2647 takes them (3 nodes). -/
def ordS8R130_Law2647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2647. -/
theorem noS8R130_Law2647 : ∀ v : Magma.tup8R130,
    ¬ @Equation2647 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2649 takes them (4 nodes). -/
def ordS8R130_Law2649 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2649. -/
theorem noS8R130_Law2649 : ∀ v : Magma.tup8R130,
    ¬ @Equation2649 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2649) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2649) (by native_decide) v.1 v.2
    ((@Law2649.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2650 takes them (3 nodes). -/
def ordS8R130_Law2650 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2650. -/
theorem noS8R130_Law2650 : ∀ v : Magma.tup8R130,
    ¬ @Equation2650 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2650) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2650) (by native_decide) v.1 v.2
    ((@Law2650.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2652 takes them (4 nodes). -/
def ordS8R130_Law2652 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2652. -/
theorem noS8R130_Law2652 : ∀ v : Magma.tup8R130,
    ¬ @Equation2652 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2652) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2652) (by native_decide) v.1 v.2
    ((@Law2652.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (3 nodes). -/
def ordS8R130_Law2653 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2653. -/
theorem noS8R130_Law2653 : ∀ v : Magma.tup8R130,
    ¬ @Equation2653 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2659 takes them (4 nodes). -/
def ordS8R130_Law2659 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2659. -/
theorem noS8R130_Law2659 : ∀ v : Magma.tup8R130,
    ¬ @Equation2659 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2659) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2659) (by native_decide) v.1 v.2
    ((@Law2659.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (3 nodes). -/
def ordS8R130_Law2660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2660. -/
theorem noS8R130_Law2660 : ∀ v : Magma.tup8R130,
    ¬ @Equation2660 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2662 takes them (4 nodes). -/
def ordS8R130_Law2662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2662. -/
theorem noS8R130_Law2662 : ∀ v : Magma.tup8R130,
    ¬ @Equation2662 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2662) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2662) (by native_decide) v.1 v.2
    ((@Law2662.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (3 nodes). -/
def ordS8R130_Law2663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2663. -/
theorem noS8R130_Law2663 : ∀ v : Magma.tup8R130,
    ¬ @Equation2663 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2670 takes them (3 nodes). -/
def ordS8R130_Law2670 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2670. -/
theorem noS8R130_Law2670 : ∀ v : Magma.tup8R130,
    ¬ @Equation2670 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2670) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2670) (by native_decide) v.1 v.2
    ((@Law2670.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2672 takes them (4 nodes). -/
def ordS8R130_Law2672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2672. -/
theorem noS8R130_Law2672 : ∀ v : Magma.tup8R130,
    ¬ @Equation2672 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2672) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2672) (by native_decide) v.1 v.2
    ((@Law2672.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (3 nodes). -/
def ordS8R130_Law2673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2673. -/
theorem noS8R130_Law2673 : ∀ v : Magma.tup8R130,
    ¬ @Equation2673 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2677 takes them (3 nodes). -/
def ordS8R130_Law2677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2677. -/
theorem noS8R130_Law2677 : ∀ v : Magma.tup8R130,
    ¬ @Equation2677 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2677) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2677) (by native_decide) v.1 v.2
    ((@Law2677.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2685 takes them (3 nodes). -/
def ordS8R130_Law2685 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2685. -/
theorem noS8R130_Law2685 : ∀ v : Magma.tup8R130,
    ¬ @Equation2685 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2685) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2685) (by native_decide) v.1 v.2
    ((@Law2685.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2687 takes them (4 nodes). -/
def ordS8R130_Law2687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2687. -/
theorem noS8R130_Law2687 : ∀ v : Magma.tup8R130,
    ¬ @Equation2687 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2687) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2687) (by native_decide) v.1 v.2
    ((@Law2687.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (3 nodes). -/
def ordS8R130_Law2688 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2688. -/
theorem noS8R130_Law2688 : ∀ v : Magma.tup8R130,
    ¬ @Equation2688 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2696 takes them (3 nodes). -/
def ordS8R130_Law2696 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2696. -/
theorem noS8R130_Law2696 : ∀ v : Magma.tup8R130,
    ¬ @Equation2696 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2696) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2696) (by native_decide) v.1 v.2
    ((@Law2696.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (3 nodes). -/
def ordS8R130_Law2699 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2699. -/
theorem noS8R130_Law2699 : ∀ v : Magma.tup8R130,
    ¬ @Equation2699 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2706 takes them (3 nodes). -/
def ordS8R130_Law2706 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2706. -/
theorem noS8R130_Law2706 : ∀ v : Magma.tup8R130,
    ¬ @Equation2706 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2706) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2706) (by native_decide) v.1 v.2
    ((@Law2706.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (3 nodes). -/
def ordS8R130_Law2709 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2709. -/
theorem noS8R130_Law2709 : ∀ v : Magma.tup8R130,
    ¬ @Equation2709 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2724 takes them (3 nodes). -/
def ordS8R130_Law2724 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2724. -/
theorem noS8R130_Law2724 : ∀ v : Magma.tup8R130,
    ¬ @Equation2724 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2724) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2724) (by native_decide) v.1 v.2
    ((@Law2724.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2733 takes them (3 nodes). -/
def ordS8R130_Law2733 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2733. -/
theorem noS8R130_Law2733 : ∀ v : Magma.tup8R130,
    ¬ @Equation2733 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2733) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2733) (by native_decide) v.1 v.2
    ((@Law2733.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (3 nodes). -/
def ordS8R130_Law2736 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2736. -/
theorem noS8R130_Law2736 : ∀ v : Magma.tup8R130,
    ¬ @Equation2736 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2743 takes them (3 nodes). -/
def ordS8R130_Law2743 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2743. -/
theorem noS8R130_Law2743 : ∀ v : Magma.tup8R130,
    ¬ @Equation2743 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2743) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2743) (by native_decide) v.1 v.2
    ((@Law2743.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2746 takes them (3 nodes). -/
def ordS8R130_Law2746 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2746. -/
theorem noS8R130_Law2746 : ∀ v : Magma.tup8R130,
    ¬ @Equation2746 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2746) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law2746) (by native_decide) v.1 v.2
    ((@Law2746.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2761 takes them (3 nodes). -/
def ordS8R130_Law2761 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2761. -/
theorem noS8R130_Law2761 : ∀ v : Magma.tup8R130,
    ¬ @Equation2761 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2761) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2761) (by native_decide) v.1 v.2
    ((@Law2761.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2770 takes them (3 nodes). -/
def ordS8R130_Law2770 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2770. -/
theorem noS8R130_Law2770 : ∀ v : Magma.tup8R130,
    ¬ @Equation2770 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2770) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2770) (by native_decide) v.1 v.2
    ((@Law2770.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2791 takes them (3 nodes). -/
def ordS8R130_Law2791 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2791. -/
theorem noS8R130_Law2791 : ∀ v : Magma.tup8R130,
    ¬ @Equation2791 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2791) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2791) (by native_decide) v.1 v.2
    ((@Law2791.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2795 takes them (3 nodes). -/
def ordS8R130_Law2795 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2795. -/
theorem noS8R130_Law2795 : ∀ v : Magma.tup8R130,
    ¬ @Equation2795 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2795) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2795) (by native_decide) v.1 v.2
    ((@Law2795.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2808 takes them (3 nodes). -/
def ordS8R130_Law2808 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2808. -/
theorem noS8R130_Law2808 : ∀ v : Magma.tup8R130,
    ¬ @Equation2808 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2808) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law2808) (by native_decide) v.1 v.2
    ((@Law2808.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_3 :
    FamilyRefutes Magma.srch8R130 [
      2079, 2087, 2090, 2097, 2124, 2137, 2152, 2161, 2186, 2199, 2240, 2243, 2246, 2249, 2253,
      2254, 2256, 2263, 2266, 2267, 2271, 2279, 2281, 2282, 2290, 2300, 2303, 2318, 2327, 2337,
      2340, 2355, 2364, 2385, 2389, 2402, 2406, 2430, 2443, 2444, 2446, 2449, 2456, 2457, 2459,
      2466, 2470, 2474, 2476, 2482, 2485, 2493, 2496, 2503, 2530, 2540, 2543, 2558, 2567, 2592,
      2605, 2646, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2662, 2663, 2670, 2672, 2673, 2677,
      2685, 2687, 2688, 2696, 2699, 2706, 2709, 2724, 2733, 2736, 2743, 2746, 2761, 2770, 2791,
      2795, 2808
    ] :=
  ⟨noS8R130_Law2079, noS8R130_Law2087, noS8R130_Law2090, noS8R130_Law2097, noS8R130_Law2124, noS8R130_Law2137, noS8R130_Law2152, noS8R130_Law2161, noS8R130_Law2186, noS8R130_Law2199, noS8R130_Law2240, noS8R130_Law2243, noS8R130_Law2246, noS8R130_Law2249, noS8R130_Law2253, noS8R130_Law2254, noS8R130_Law2256, noS8R130_Law2263, noS8R130_Law2266, noS8R130_Law2267, noS8R130_Law2271, noS8R130_Law2279, noS8R130_Law2281, noS8R130_Law2282, noS8R130_Law2290, noS8R130_Law2300, noS8R130_Law2303, noS8R130_Law2318, noS8R130_Law2327, noS8R130_Law2337, noS8R130_Law2340, noS8R130_Law2355, noS8R130_Law2364, noS8R130_Law2385, noS8R130_Law2389, noS8R130_Law2402, noS8R130_Law2406, noS8R130_Law2430, noS8R130_Law2443, noS8R130_Law2444, noS8R130_Law2446, noS8R130_Law2449, noS8R130_Law2456, noS8R130_Law2457, noS8R130_Law2459, noS8R130_Law2466, noS8R130_Law2470, noS8R130_Law2474, noS8R130_Law2476, noS8R130_Law2482, noS8R130_Law2485, noS8R130_Law2493, noS8R130_Law2496, noS8R130_Law2503, noS8R130_Law2530, noS8R130_Law2540, noS8R130_Law2543, noS8R130_Law2558, noS8R130_Law2567, noS8R130_Law2592, noS8R130_Law2605, noS8R130_Law2646, noS8R130_Law2647, noS8R130_Law2649, noS8R130_Law2650, noS8R130_Law2652, noS8R130_Law2653, noS8R130_Law2659, noS8R130_Law2660, noS8R130_Law2662, noS8R130_Law2663, noS8R130_Law2670, noS8R130_Law2672, noS8R130_Law2673, noS8R130_Law2677, noS8R130_Law2685, noS8R130_Law2687, noS8R130_Law2688, noS8R130_Law2696, noS8R130_Law2699, noS8R130_Law2706, noS8R130_Law2709, noS8R130_Law2724, noS8R130_Law2733, noS8R130_Law2736, noS8R130_Law2743, noS8R130_Law2746, noS8R130_Law2761, noS8R130_Law2770, noS8R130_Law2791, noS8R130_Law2795, noS8R130_Law2808⟩

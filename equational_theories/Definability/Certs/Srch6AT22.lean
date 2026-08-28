import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 23 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `23`
equations here, 3,015 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2241 takes them (489 nodes). -/
def ordS6A_Law2241 : List (Fin 11) := [2, 5, 4, 1, 8, 3, 0, 9, 10, 7, 6]

/-- No member of the class satisfies equation 2241. -/
theorem noS6A_Law2241 : ∀ v : Magma.tupS6A,
    ¬ @Equation2241 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2242 takes them (53 nodes). -/
def ordS6A_Law2242 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2242. -/
theorem noS6A_Law2242 : ∀ v : Magma.tupS6A,
    ¬ @Equation2242 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2242) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2242) (by native_decide) v.1 v.2
    ((@Law2242.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2245 takes them (84 nodes). -/
def ordS6A_Law2245 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2245. -/
theorem noS6A_Law2245 : ∀ v : Magma.tupS6A,
    ¬ @Equation2245 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2245) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2245) (by native_decide) v.1 v.2
    ((@Law2245.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2247 takes them (354 nodes). -/
def ordS6A_Law2247 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2247. -/
theorem noS6A_Law2247 : ∀ v : Magma.tupS6A,
    ¬ @Equation2247 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2247) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2247) (by native_decide) v.1 v.2
    ((@Law2247.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2248 takes them (107 nodes). -/
def ordS6A_Law2248 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2248. -/
theorem noS6A_Law2248 : ∀ v : Magma.tupS6A,
    ¬ @Equation2248 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2248) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2248) (by native_decide) v.1 v.2
    ((@Law2248.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2250 takes them (129 nodes). -/
def ordS6A_Law2250 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2250. -/
theorem noS6A_Law2250 : ∀ v : Magma.tupS6A,
    ¬ @Equation2250 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2250) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2250) (by native_decide) v.1 v.2
    ((@Law2250.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2251 takes them (104 nodes). -/
def ordS6A_Law2251 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2251. -/
theorem noS6A_Law2251 : ∀ v : Magma.tupS6A,
    ¬ @Equation2251 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2251) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2251) (by native_decide) v.1 v.2
    ((@Law2251.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2252 takes them (43 nodes). -/
def ordS6A_Law2252 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2252. -/
theorem noS6A_Law2252 : ∀ v : Magma.tupS6A,
    ¬ @Equation2252 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2252) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2252) (by native_decide) v.1 v.2
    ((@Law2252.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2255 takes them (103 nodes). -/
def ordS6A_Law2255 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2255. -/
theorem noS6A_Law2255 : ∀ v : Magma.tupS6A,
    ¬ @Equation2255 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2255) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2255) (by native_decide) v.1 v.2
    ((@Law2255.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2258 takes them (80 nodes). -/
def ordS6A_Law2258 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2258. -/
theorem noS6A_Law2258 : ∀ v : Magma.tupS6A,
    ¬ @Equation2258 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2258) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2258) (by native_decide) v.1 v.2
    ((@Law2258.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2261 takes them (120 nodes). -/
def ordS6A_Law2261 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2261. -/
theorem noS6A_Law2261 : ∀ v : Magma.tupS6A,
    ¬ @Equation2261 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2261) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2261) (by native_decide) v.1 v.2
    ((@Law2261.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2262 takes them (33 nodes). -/
def ordS6A_Law2262 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2262. -/
theorem noS6A_Law2262 : ∀ v : Magma.tupS6A,
    ¬ @Equation2262 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2262) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2262) (by native_decide) v.1 v.2
    ((@Law2262.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2265 takes them (94 nodes). -/
def ordS6A_Law2265 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2265. -/
theorem noS6A_Law2265 : ∀ v : Magma.tupS6A,
    ¬ @Equation2265 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2265) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2265) (by native_decide) v.1 v.2
    ((@Law2265.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2268 takes them (82 nodes). -/
def ordS6A_Law2268 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2268. -/
theorem noS6A_Law2268 : ∀ v : Magma.tupS6A,
    ¬ @Equation2268 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2268) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2268) (by native_decide) v.1 v.2
    ((@Law2268.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2271 takes them (204 nodes). -/
def ordS6A_Law2271 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2271. -/
theorem noS6A_Law2271 : ∀ v : Magma.tupS6A,
    ¬ @Equation2271 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2271) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2271) (by native_decide) v.1 v.2
    ((@Law2271.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2272 takes them (40 nodes). -/
def ordS6A_Law2272 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2272. -/
theorem noS6A_Law2272 : ∀ v : Magma.tupS6A,
    ¬ @Equation2272 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2272) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2272) (by native_decide) v.1 v.2
    ((@Law2272.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2275 takes them (165 nodes). -/
def ordS6A_Law2275 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2275. -/
theorem noS6A_Law2275 : ∀ v : Magma.tupS6A,
    ¬ @Equation2275 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2275) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2275) (by native_decide) v.1 v.2
    ((@Law2275.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2276 takes them (66 nodes). -/
def ordS6A_Law2276 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2276. -/
theorem noS6A_Law2276 : ∀ v : Magma.tupS6A,
    ¬ @Equation2276 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2276) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2276) (by native_decide) v.1 v.2
    ((@Law2276.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (286 nodes). -/
def ordS6A_Law2279 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2279. -/
theorem noS6A_Law2279 : ∀ v : Magma.tupS6A,
    ¬ @Equation2279 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2280 takes them (66 nodes). -/
def ordS6A_Law2280 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2280. -/
theorem noS6A_Law2280 : ∀ v : Magma.tupS6A,
    ¬ @Equation2280 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2280) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2280) (by native_decide) v.1 v.2
    ((@Law2280.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2283 takes them (145 nodes). -/
def ordS6A_Law2283 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2283. -/
theorem noS6A_Law2283 : ∀ v : Magma.tupS6A,
    ¬ @Equation2283 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2283) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2283) (by native_decide) v.1 v.2
    ((@Law2283.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2284 takes them (82 nodes). -/
def ordS6A_Law2284 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2284. -/
theorem noS6A_Law2284 : ∀ v : Magma.tupS6A,
    ¬ @Equation2284 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2284) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2284) (by native_decide) v.1 v.2
    ((@Law2284.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2287 takes them (86 nodes). -/
def ordS6A_Law2287 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2287. -/
theorem noS6A_Law2287 : ∀ v : Magma.tupS6A,
    ¬ @Equation2287 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2287) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2287) (by native_decide) v.1 v.2
    ((@Law2287.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `23` equations. -/
theorem srch6A_refutes_22 :
    FamilyRefutes Magma.srch6A [
      2241, 2242, 2245, 2247, 2248, 2250, 2251, 2252, 2255, 2258, 2261, 2262, 2265, 2268, 2271,
      2272, 2275, 2276, 2279, 2280, 2283, 2284, 2287
    ] :=
  ⟨noS6A_Law2241, noS6A_Law2242, noS6A_Law2245, noS6A_Law2247, noS6A_Law2248, noS6A_Law2250, noS6A_Law2251, noS6A_Law2252, noS6A_Law2255, noS6A_Law2258, noS6A_Law2261, noS6A_Law2262, noS6A_Law2265, noS6A_Law2268, noS6A_Law2271, noS6A_Law2272, noS6A_Law2275, noS6A_Law2276, noS6A_Law2279, noS6A_Law2280, noS6A_Law2283, noS6A_Law2284, noS6A_Law2287⟩

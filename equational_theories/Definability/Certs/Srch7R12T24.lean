import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 25 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `15` equations here, 2,688 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2273 takes them (448 nodes). -/
def ordS7R12_Law2273 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2273. -/
theorem noS7R12_Law2273 : ∀ v : Magma.tup7R12,
    ¬ @Equation2273 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2273) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2273) (by native_decide) v.1 v.2
    ((@Law2273.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2277 takes them (336 nodes). -/
def ordS7R12_Law2277 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2277. -/
theorem noS7R12_Law2277 : ∀ v : Magma.tup7R12,
    ¬ @Equation2277 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2277) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2277) (by native_decide) v.1 v.2
    ((@Law2277.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2282 takes them (382 nodes). -/
def ordS7R12_Law2282 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2282. -/
theorem noS7R12_Law2282 : ∀ v : Magma.tup7R12,
    ¬ @Equation2282 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2282) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2282) (by native_decide) v.1 v.2
    ((@Law2282.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2285 takes them (248 nodes). -/
def ordS7R12_Law2285 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2285. -/
theorem noS7R12_Law2285 : ∀ v : Magma.tup7R12,
    ¬ @Equation2285 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2285) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2285) (by native_decide) v.1 v.2
    ((@Law2285.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2306 takes them (105 nodes). -/
def ordS7R12_Law2306 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2306. -/
theorem noS7R12_Law2306 : ∀ v : Magma.tup7R12,
    ¬ @Equation2306 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2306) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2306) (by native_decide) v.1 v.2
    ((@Law2306.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2310 takes them (189 nodes). -/
def ordS7R12_Law2310 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2310. -/
theorem noS7R12_Law2310 : ∀ v : Magma.tup7R12,
    ¬ @Equation2310 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2310) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2310) (by native_decide) v.1 v.2
    ((@Law2310.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2314 takes them (119 nodes). -/
def ordS7R12_Law2314 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2314. -/
theorem noS7R12_Law2314 : ∀ v : Magma.tup7R12,
    ¬ @Equation2314 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2314) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2314) (by native_decide) v.1 v.2
    ((@Law2314.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2347 takes them (112 nodes). -/
def ordS7R12_Law2347 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2347. -/
theorem noS7R12_Law2347 : ∀ v : Magma.tup7R12,
    ¬ @Equation2347 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2347) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2347) (by native_decide) v.1 v.2
    ((@Law2347.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2368 takes them (130 nodes). -/
def ordS7R12_Law2368 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2368. -/
theorem noS7R12_Law2368 : ∀ v : Magma.tup7R12,
    ¬ @Equation2368 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2368) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2368) (by native_decide) v.1 v.2
    ((@Law2368.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2372 takes them (179 nodes). -/
def ordS7R12_Law2372 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2372. -/
theorem noS7R12_Law2372 : ∀ v : Magma.tup7R12,
    ¬ @Equation2372 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2372) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2372) (by native_decide) v.1 v.2
    ((@Law2372.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2381 takes them (79 nodes). -/
def ordS7R12_Law2381 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2381. -/
theorem noS7R12_Law2381 : ∀ v : Magma.tup7R12,
    ¬ @Equation2381 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2381) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2381) (by native_decide) v.1 v.2
    ((@Law2381.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2398 takes them (112 nodes). -/
def ordS7R12_Law2398 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2398. -/
theorem noS7R12_Law2398 : ∀ v : Magma.tup7R12,
    ¬ @Equation2398 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2398) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2398) (by native_decide) v.1 v.2
    ((@Law2398.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2415 takes them (64 nodes). -/
def ordS7R12_Law2415 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2415. -/
theorem noS7R12_Law2415 : ∀ v : Magma.tup7R12,
    ¬ @Equation2415 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2415) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2415) (by native_decide) v.1 v.2
    ((@Law2415.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2420 takes them (78 nodes). -/
def ordS7R12_Law2420 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2420. -/
theorem noS7R12_Law2420 : ∀ v : Magma.tup7R12,
    ¬ @Equation2420 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2420) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2420) (by native_decide) v.1 v.2
    ((@Law2420.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2425 takes them (107 nodes). -/
def ordS7R12_Law2425 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2425. -/
theorem noS7R12_Law2425 : ∀ v : Magma.tup7R12,
    ¬ @Equation2425 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2425) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2425) (by native_decide) v.1 v.2
    ((@Law2425.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srch7R12_refutes_24 :
    FamilyRefutes Magma.srch7R12 [
      2273, 2277, 2282, 2285, 2306, 2310, 2314, 2347, 2368, 2372, 2381, 2398, 2415, 2420, 2425
    ] :=
  ⟨noS7R12_Law2273, noS7R12_Law2277, noS7R12_Law2282, noS7R12_Law2285, noS7R12_Law2306, noS7R12_Law2310, noS7R12_Law2314, noS7R12_Law2347, noS7R12_Law2368, noS7R12_Law2372, noS7R12_Law2381, noS7R12_Law2398, noS7R12_Law2415, noS7R12_Law2420, noS7R12_Law2425⟩

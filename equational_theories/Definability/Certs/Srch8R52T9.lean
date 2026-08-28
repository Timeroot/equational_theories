import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 10 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,155 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2282 takes them (249 nodes). -/
def ordS8R52_Law2282 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2282. -/
theorem noS8R52_Law2282 : ∀ v : Magma.tup8R52,
    ¬ @Equation2282 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2282) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2282) (by native_decide) v.1 v.2
    ((@Law2282.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2286 takes them (217 nodes). -/
def ordS8R52_Law2286 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2286. -/
theorem noS8R52_Law2286 : ∀ v : Magma.tup8R52,
    ¬ @Equation2286 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2286) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2286) (by native_decide) v.1 v.2
    ((@Law2286.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2290 takes them (406 nodes). -/
def ordS8R52_Law2290 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2290. -/
theorem noS8R52_Law2290 : ∀ v : Magma.tup8R52,
    ¬ @Equation2290 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2290) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2290) (by native_decide) v.1 v.2
    ((@Law2290.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2310 takes them (166 nodes). -/
def ordS8R52_Law2310 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2310. -/
theorem noS8R52_Law2310 : ∀ v : Magma.tup8R52,
    ¬ @Equation2310 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2310) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2310) (by native_decide) v.1 v.2
    ((@Law2310.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2337 takes them (302 nodes). -/
def ordS8R52_Law2337 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2337. -/
theorem noS8R52_Law2337 : ∀ v : Magma.tup8R52,
    ¬ @Equation2337 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2337) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2337) (by native_decide) v.1 v.2
    ((@Law2337.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2347 takes them (146 nodes). -/
def ordS8R52_Law2347 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2347. -/
theorem noS8R52_Law2347 : ∀ v : Magma.tup8R52,
    ¬ @Equation2347 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2347) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2347) (by native_decide) v.1 v.2
    ((@Law2347.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2364 takes them (178 nodes). -/
def ordS8R52_Law2364 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2364. -/
theorem noS8R52_Law2364 : ∀ v : Magma.tup8R52,
    ¬ @Equation2364 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2364) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2364) (by native_decide) v.1 v.2
    ((@Law2364.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2381 takes them (146 nodes). -/
def ordS8R52_Law2381 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2381. -/
theorem noS8R52_Law2381 : ∀ v : Magma.tup8R52,
    ¬ @Equation2381 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2381) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2381) (by native_decide) v.1 v.2
    ((@Law2381.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2398 takes them (146 nodes). -/
def ordS8R52_Law2398 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2398. -/
theorem noS8R52_Law2398 : ∀ v : Magma.tup8R52,
    ¬ @Equation2398 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2398) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2398) (by native_decide) v.1 v.2
    ((@Law2398.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2415 takes them (146 nodes). -/
def ordS8R52_Law2415 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2415. -/
theorem noS8R52_Law2415 : ∀ v : Magma.tup8R52,
    ¬ @Equation2415 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2415) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2415) (by native_decide) v.1 v.2
    ((@Law2415.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (505 nodes). -/
def ordS8R52_Law2457 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R52_Law2457 : ∀ v : Magma.tup8R52,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2493 takes them (406 nodes). -/
def ordS8R52_Law2493 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2493. -/
theorem noS8R52_Law2493 : ∀ v : Magma.tup8R52,
    ¬ @Equation2493 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2493) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2493) (by native_decide) v.1 v.2
    ((@Law2493.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2513 takes them (142 nodes). -/
def ordS8R52_Law2513 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2513. -/
theorem noS8R52_Law2513 : ∀ v : Magma.tup8R52,
    ¬ @Equation2513 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2513) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2513) (by native_decide) v.1 v.2
    ((@Law2513.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch8R52_refutes_9 :
    FamilyRefutes Magma.srch8R52 [
      2282, 2286, 2290, 2310, 2337, 2347, 2364, 2381, 2398, 2415, 2457, 2493, 2513
    ] :=
  ⟨noS8R52_Law2282, noS8R52_Law2286, noS8R52_Law2290, noS8R52_Law2310, noS8R52_Law2337, noS8R52_Law2347, noS8R52_Law2364, noS8R52_Law2381, noS8R52_Law2398, noS8R52_Law2415, noS8R52_Law2457, noS8R52_Law2493, noS8R52_Law2513⟩

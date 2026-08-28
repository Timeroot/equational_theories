import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 24 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `23`
equations here, 2,865 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2288 takes them (84 nodes). -/
def ordS6A_Law2288 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2288. -/
theorem noS6A_Law2288 : ∀ v : Magma.tupS6A,
    ¬ @Equation2288 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2288) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2288) (by native_decide) v.1 v.2
    ((@Law2288.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2289 takes them (33 nodes). -/
def ordS6A_Law2289 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2289. -/
theorem noS6A_Law2289 : ∀ v : Magma.tupS6A,
    ¬ @Equation2289 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2289) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2289) (by native_decide) v.1 v.2
    ((@Law2289.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2343 takes them (38 nodes). -/
def ordS6A_Law2343 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2343. -/
theorem noS6A_Law2343 : ∀ v : Magma.tupS6A,
    ¬ @Equation2343 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2343) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2343) (by native_decide) v.1 v.2
    ((@Law2343.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2359 takes them (36 nodes). -/
def ordS6A_Law2359 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2359. -/
theorem noS6A_Law2359 : ∀ v : Magma.tupS6A,
    ¬ @Equation2359 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2359) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2359) (by native_decide) v.1 v.2
    ((@Law2359.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2393 takes them (29 nodes). -/
def ordS6A_Law2393 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2393. -/
theorem noS6A_Law2393 : ∀ v : Magma.tupS6A,
    ¬ @Equation2393 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2393) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2393) (by native_decide) v.1 v.2
    ((@Law2393.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2410 takes them (36 nodes). -/
def ordS6A_Law2410 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2410. -/
theorem noS6A_Law2410 : ∀ v : Magma.tupS6A,
    ¬ @Equation2410 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2410) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2410) (by native_decide) v.1 v.2
    ((@Law2410.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2435 takes them (29 nodes). -/
def ordS6A_Law2435 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2435. -/
theorem noS6A_Law2435 : ∀ v : Magma.tupS6A,
    ¬ @Equation2435 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2435) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2435) (by native_decide) v.1 v.2
    ((@Law2435.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2442 takes them (141 nodes). -/
def ordS6A_Law2442 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2442. -/
theorem noS6A_Law2442 : ∀ v : Magma.tupS6A,
    ¬ @Equation2442 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2442) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2442) (by native_decide) v.1 v.2
    ((@Law2442.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2445 takes them (124 nodes). -/
def ordS6A_Law2445 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2445. -/
theorem noS6A_Law2445 : ∀ v : Magma.tupS6A,
    ¬ @Equation2445 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2445) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2445) (by native_decide) v.1 v.2
    ((@Law2445.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2447 takes them (793 nodes). -/
def ordS6A_Law2447 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2447. -/
theorem noS6A_Law2447 : ∀ v : Magma.tupS6A,
    ¬ @Equation2447 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2447) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2447) (by native_decide) v.1 v.2
    ((@Law2447.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2448 takes them (53 nodes). -/
def ordS6A_Law2448 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2448. -/
theorem noS6A_Law2448 : ∀ v : Magma.tupS6A,
    ¬ @Equation2448 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2448) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2448) (by native_decide) v.1 v.2
    ((@Law2448.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2450 takes them (330 nodes). -/
def ordS6A_Law2450 : List (Fin 11) := [10, 2, 0, 6, 9, 5, 1, 4, 7, 8, 3]

/-- No member of the class satisfies equation 2450. -/
theorem noS6A_Law2450 : ∀ v : Magma.tupS6A,
    ¬ @Equation2450 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2450) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2450) (by native_decide) v.1 v.2
    ((@Law2450.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2451 takes them (89 nodes). -/
def ordS6A_Law2451 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2451. -/
theorem noS6A_Law2451 : ∀ v : Magma.tupS6A,
    ¬ @Equation2451 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2451) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2451) (by native_decide) v.1 v.2
    ((@Law2451.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2453 takes them (165 nodes). -/
def ordS6A_Law2453 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2453. -/
theorem noS6A_Law2453 : ∀ v : Magma.tupS6A,
    ¬ @Equation2453 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2453) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2453) (by native_decide) v.1 v.2
    ((@Law2453.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2454 takes them (114 nodes). -/
def ordS6A_Law2454 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2454. -/
theorem noS6A_Law2454 : ∀ v : Magma.tupS6A,
    ¬ @Equation2454 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2454) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2454) (by native_decide) v.1 v.2
    ((@Law2454.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2455 takes them (41 nodes). -/
def ordS6A_Law2455 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2455. -/
theorem noS6A_Law2455 : ∀ v : Magma.tupS6A,
    ¬ @Equation2455 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2455) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2455) (by native_decide) v.1 v.2
    ((@Law2455.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2458 takes them (68 nodes). -/
def ordS6A_Law2458 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2458. -/
theorem noS6A_Law2458 : ∀ v : Magma.tupS6A,
    ¬ @Equation2458 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2458) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2458) (by native_decide) v.1 v.2
    ((@Law2458.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2461 takes them (82 nodes). -/
def ordS6A_Law2461 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2461. -/
theorem noS6A_Law2461 : ∀ v : Magma.tupS6A,
    ¬ @Equation2461 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2461) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2461) (by native_decide) v.1 v.2
    ((@Law2461.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2463 takes them (207 nodes). -/
def ordS6A_Law2463 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2463. -/
theorem noS6A_Law2463 : ∀ v : Magma.tupS6A,
    ¬ @Equation2463 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2463) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2463) (by native_decide) v.1 v.2
    ((@Law2463.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2464 takes them (106 nodes). -/
def ordS6A_Law2464 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2464. -/
theorem noS6A_Law2464 : ∀ v : Magma.tupS6A,
    ¬ @Equation2464 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2464) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2464) (by native_decide) v.1 v.2
    ((@Law2464.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2465 takes them (61 nodes). -/
def ordS6A_Law2465 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2465. -/
theorem noS6A_Law2465 : ∀ v : Magma.tupS6A,
    ¬ @Equation2465 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2465) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2465) (by native_decide) v.1 v.2
    ((@Law2465.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2468 takes them (103 nodes). -/
def ordS6A_Law2468 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2468. -/
theorem noS6A_Law2468 : ∀ v : Magma.tupS6A,
    ¬ @Equation2468 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2468) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2468) (by native_decide) v.1 v.2
    ((@Law2468.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2471 takes them (103 nodes). -/
def ordS6A_Law2471 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2471. -/
theorem noS6A_Law2471 : ∀ v : Magma.tupS6A,
    ¬ @Equation2471 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2471) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2471) (by native_decide) v.1 v.2
    ((@Law2471.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `23` equations. -/
theorem srch6A_refutes_23 :
    FamilyRefutes Magma.srch6A [
      2288, 2289, 2343, 2359, 2393, 2410, 2435, 2442, 2445, 2447, 2448, 2450, 2451, 2453, 2454,
      2455, 2458, 2461, 2463, 2464, 2465, 2468, 2471
    ] :=
  ⟨noS6A_Law2288, noS6A_Law2289, noS6A_Law2343, noS6A_Law2359, noS6A_Law2393, noS6A_Law2410, noS6A_Law2435, noS6A_Law2442, noS6A_Law2445, noS6A_Law2447, noS6A_Law2448, noS6A_Law2450, noS6A_Law2451, noS6A_Law2453, noS6A_Law2454, noS6A_Law2455, noS6A_Law2458, noS6A_Law2461, noS6A_Law2463, noS6A_Law2464, noS6A_Law2465, noS6A_Law2468, noS6A_Law2471⟩

import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 25 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `27`
equations here, 2,871 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2473 takes them (210 nodes). -/
def ordS6A_Law2473 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2473. -/
theorem noS6A_Law2473 : ∀ v : Magma.tupS6A,
    ¬ @Equation2473 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2473) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2473) (by native_decide) v.1 v.2
    ((@Law2473.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2475 takes them (103 nodes). -/
def ordS6A_Law2475 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2475. -/
theorem noS6A_Law2475 : ∀ v : Magma.tupS6A,
    ¬ @Equation2475 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2475) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2475) (by native_decide) v.1 v.2
    ((@Law2475.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2477 takes them (144 nodes). -/
def ordS6A_Law2477 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2477. -/
theorem noS6A_Law2477 : ∀ v : Magma.tupS6A,
    ¬ @Equation2477 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2477) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2477) (by native_decide) v.1 v.2
    ((@Law2477.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2478 takes them (96 nodes). -/
def ordS6A_Law2478 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2478. -/
theorem noS6A_Law2478 : ∀ v : Magma.tupS6A,
    ¬ @Equation2478 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2478) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2478) (by native_decide) v.1 v.2
    ((@Law2478.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2479 takes them (40 nodes). -/
def ordS6A_Law2479 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2479. -/
theorem noS6A_Law2479 : ∀ v : Magma.tupS6A,
    ¬ @Equation2479 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2479) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2479) (by native_decide) v.1 v.2
    ((@Law2479.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2481 takes them (203 nodes). -/
def ordS6A_Law2481 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2481. -/
theorem noS6A_Law2481 : ∀ v : Magma.tupS6A,
    ¬ @Equation2481 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2481) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2481) (by native_decide) v.1 v.2
    ((@Law2481.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2482 takes them (253 nodes). -/
def ordS6A_Law2482 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2482. -/
theorem noS6A_Law2482 : ∀ v : Magma.tupS6A,
    ¬ @Equation2482 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2482) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2482) (by native_decide) v.1 v.2
    ((@Law2482.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2483 takes them (40 nodes). -/
def ordS6A_Law2483 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2483. -/
theorem noS6A_Law2483 : ∀ v : Magma.tupS6A,
    ¬ @Equation2483 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2483) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2483) (by native_decide) v.1 v.2
    ((@Law2483.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2486 takes them (114 nodes). -/
def ordS6A_Law2486 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2486. -/
theorem noS6A_Law2486 : ∀ v : Magma.tupS6A,
    ¬ @Equation2486 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2486) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2486) (by native_decide) v.1 v.2
    ((@Law2486.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2487 takes them (65 nodes). -/
def ordS6A_Law2487 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2487. -/
theorem noS6A_Law2487 : ∀ v : Magma.tupS6A,
    ¬ @Equation2487 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2487) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2487) (by native_decide) v.1 v.2
    ((@Law2487.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2489 takes them (129 nodes). -/
def ordS6A_Law2489 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2489. -/
theorem noS6A_Law2489 : ∀ v : Magma.tupS6A,
    ¬ @Equation2489 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2489) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2489) (by native_decide) v.1 v.2
    ((@Law2489.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2490 takes them (87 nodes). -/
def ordS6A_Law2490 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2490. -/
theorem noS6A_Law2490 : ∀ v : Magma.tupS6A,
    ¬ @Equation2490 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2490) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2490) (by native_decide) v.1 v.2
    ((@Law2490.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2491 takes them (68 nodes). -/
def ordS6A_Law2491 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2491. -/
theorem noS6A_Law2491 : ∀ v : Magma.tupS6A,
    ¬ @Equation2491 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2491) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2491) (by native_decide) v.1 v.2
    ((@Law2491.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2492 takes them (33 nodes). -/
def ordS6A_Law2492 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2492. -/
theorem noS6A_Law2492 : ∀ v : Magma.tupS6A,
    ¬ @Equation2492 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2492) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2492) (by native_decide) v.1 v.2
    ((@Law2492.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2509 takes them (131 nodes). -/
def ordS6A_Law2509 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2509. -/
theorem noS6A_Law2509 : ∀ v : Magma.tupS6A,
    ¬ @Equation2509 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2509) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2509) (by native_decide) v.1 v.2
    ((@Law2509.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2521 takes them (186 nodes). -/
def ordS6A_Law2521 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2521. -/
theorem noS6A_Law2521 : ∀ v : Magma.tupS6A,
    ¬ @Equation2521 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2521) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2521) (by native_decide) v.1 v.2
    ((@Law2521.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2525 takes them (88 nodes). -/
def ordS6A_Law2525 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2525. -/
theorem noS6A_Law2525 : ∀ v : Magma.tupS6A,
    ¬ @Equation2525 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2525) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2525) (by native_decide) v.1 v.2
    ((@Law2525.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2546 takes them (135 nodes). -/
def ordS6A_Law2546 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2546. -/
theorem noS6A_Law2546 : ∀ v : Magma.tupS6A,
    ¬ @Equation2546 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2546) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2546) (by native_decide) v.1 v.2
    ((@Law2546.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2562 takes them (43 nodes). -/
def ordS6A_Law2562 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2562. -/
theorem noS6A_Law2562 : ∀ v : Magma.tupS6A,
    ¬ @Equation2562 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2562) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2562) (by native_decide) v.1 v.2
    ((@Law2562.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2575 takes them (80 nodes). -/
def ordS6A_Law2575 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2575. -/
theorem noS6A_Law2575 : ∀ v : Magma.tupS6A,
    ¬ @Equation2575 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2575) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2575) (by native_decide) v.1 v.2
    ((@Law2575.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2579 takes them (69 nodes). -/
def ordS6A_Law2579 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2579. -/
theorem noS6A_Law2579 : ∀ v : Magma.tupS6A,
    ¬ @Equation2579 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2579) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2579) (by native_decide) v.1 v.2
    ((@Law2579.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2596 takes them (57 nodes). -/
def ordS6A_Law2596 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2596. -/
theorem noS6A_Law2596 : ∀ v : Magma.tupS6A,
    ¬ @Equation2596 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2596) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2596) (by native_decide) v.1 v.2
    ((@Law2596.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2613 takes them (99 nodes). -/
def ordS6A_Law2613 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2613. -/
theorem noS6A_Law2613 : ∀ v : Magma.tupS6A,
    ¬ @Equation2613 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2613) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2613) (by native_decide) v.1 v.2
    ((@Law2613.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2628 takes them (36 nodes). -/
def ordS6A_Law2628 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2628. -/
theorem noS6A_Law2628 : ∀ v : Magma.tupS6A,
    ¬ @Equation2628 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2628) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2628) (by native_decide) v.1 v.2
    ((@Law2628.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2633 takes them (67 nodes). -/
def ordS6A_Law2633 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2633. -/
theorem noS6A_Law2633 : ∀ v : Magma.tupS6A,
    ¬ @Equation2633 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2633) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2633) (by native_decide) v.1 v.2
    ((@Law2633.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2638 takes them (29 nodes). -/
def ordS6A_Law2638 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2638. -/
theorem noS6A_Law2638 : ∀ v : Magma.tupS6A,
    ¬ @Equation2638 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2638) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2638) (by native_decide) v.1 v.2
    ((@Law2638.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2645 takes them (266 nodes). -/
def ordS6A_Law2645 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2645. -/
theorem noS6A_Law2645 : ∀ v : Magma.tupS6A,
    ¬ @Equation2645 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2645) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2645) (by native_decide) v.1 v.2
    ((@Law2645.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `27` equations. -/
theorem srch6A_refutes_24 :
    FamilyRefutes Magma.srch6A [
      2473, 2475, 2477, 2478, 2479, 2481, 2482, 2483, 2486, 2487, 2489, 2490, 2491, 2492, 2509,
      2521, 2525, 2546, 2562, 2575, 2579, 2596, 2613, 2628, 2633, 2638, 2645
    ] :=
  ⟨noS6A_Law2473, noS6A_Law2475, noS6A_Law2477, noS6A_Law2478, noS6A_Law2479, noS6A_Law2481, noS6A_Law2482, noS6A_Law2483, noS6A_Law2486, noS6A_Law2487, noS6A_Law2489, noS6A_Law2490, noS6A_Law2491, noS6A_Law2492, noS6A_Law2509, noS6A_Law2521, noS6A_Law2525, noS6A_Law2546, noS6A_Law2562, noS6A_Law2575, noS6A_Law2579, noS6A_Law2596, noS6A_Law2613, noS6A_Law2628, noS6A_Law2633, noS6A_Law2638, noS6A_Law2645⟩

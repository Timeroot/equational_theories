import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 13 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `20`
equations here, 2,948 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1461 takes them (221 nodes). -/
def ordS6A_Law1461 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1461. -/
theorem noS6A_Law1461 : ∀ v : Magma.tupS6A,
    ¬ @Equation1461 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1461) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1461) (by native_decide) v.1 v.2
    ((@Law1461.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1462 takes them (103 nodes). -/
def ordS6A_Law1462 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1462. -/
theorem noS6A_Law1462 : ∀ v : Magma.tupS6A,
    ¬ @Equation1462 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1462) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1462) (by native_decide) v.1 v.2
    ((@Law1462.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1463 takes them (75 nodes). -/
def ordS6A_Law1463 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1463. -/
theorem noS6A_Law1463 : ∀ v : Magma.tupS6A,
    ¬ @Equation1463 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1463) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1463) (by native_decide) v.1 v.2
    ((@Law1463.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1464 takes them (45 nodes). -/
def ordS6A_Law1464 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1464. -/
theorem noS6A_Law1464 : ∀ v : Magma.tupS6A,
    ¬ @Equation1464 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1464) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1464) (by native_decide) v.1 v.2
    ((@Law1464.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1465 takes them (204 nodes). -/
def ordS6A_Law1465 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1465. -/
theorem noS6A_Law1465 : ∀ v : Magma.tupS6A,
    ¬ @Equation1465 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1465) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1465) (by native_decide) v.1 v.2
    ((@Law1465.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1466 takes them (154 nodes). -/
def ordS6A_Law1466 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1466. -/
theorem noS6A_Law1466 : ∀ v : Magma.tupS6A,
    ¬ @Equation1466 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1466) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1466) (by native_decide) v.1 v.2
    ((@Law1466.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (261 nodes). -/
def ordS6A_Law1467 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1467. -/
theorem noS6A_Law1467 : ∀ v : Magma.tupS6A,
    ¬ @Equation1467 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1468 takes them (87 nodes). -/
def ordS6A_Law1468 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1468. -/
theorem noS6A_Law1468 : ∀ v : Magma.tupS6A,
    ¬ @Equation1468 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1468) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1468) (by native_decide) v.1 v.2
    ((@Law1468.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1469 takes them (166 nodes). -/
def ordS6A_Law1469 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1469. -/
theorem noS6A_Law1469 : ∀ v : Magma.tupS6A,
    ¬ @Equation1469 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1469) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1469) (by native_decide) v.1 v.2
    ((@Law1469.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1470 takes them (186 nodes). -/
def ordS6A_Law1470 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1470. -/
theorem noS6A_Law1470 : ∀ v : Magma.tupS6A,
    ¬ @Equation1470 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1470) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1470) (by native_decide) v.1 v.2
    ((@Law1470.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1471 takes them (69 nodes). -/
def ordS6A_Law1471 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1471. -/
theorem noS6A_Law1471 : ∀ v : Magma.tupS6A,
    ¬ @Equation1471 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1471) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1471) (by native_decide) v.1 v.2
    ((@Law1471.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1472 takes them (40 nodes). -/
def ordS6A_Law1472 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1472. -/
theorem noS6A_Law1472 : ∀ v : Magma.tupS6A,
    ¬ @Equation1472 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1472) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1472) (by native_decide) v.1 v.2
    ((@Law1472.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1473 takes them (121 nodes). -/
def ordS6A_Law1473 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1473. -/
theorem noS6A_Law1473 : ∀ v : Magma.tupS6A,
    ¬ @Equation1473 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1473) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1473) (by native_decide) v.1 v.2
    ((@Law1473.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1474 takes them (74 nodes). -/
def ordS6A_Law1474 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1474. -/
theorem noS6A_Law1474 : ∀ v : Magma.tupS6A,
    ¬ @Equation1474 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1474) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1474) (by native_decide) v.1 v.2
    ((@Law1474.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1475 takes them (65 nodes). -/
def ordS6A_Law1475 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1475. -/
theorem noS6A_Law1475 : ∀ v : Magma.tupS6A,
    ¬ @Equation1475 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1475) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1475) (by native_decide) v.1 v.2
    ((@Law1475.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1476 takes them (69 nodes). -/
def ordS6A_Law1476 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1476. -/
theorem noS6A_Law1476 : ∀ v : Magma.tupS6A,
    ¬ @Equation1476 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1476) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1476) (by native_decide) v.1 v.2
    ((@Law1476.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1477 takes them (40 nodes). -/
def ordS6A_Law1477 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1477. -/
theorem noS6A_Law1477 : ∀ v : Magma.tupS6A,
    ¬ @Equation1477 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1477) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1477) (by native_decide) v.1 v.2
    ((@Law1477.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1479 takes them (491 nodes). -/
def ordS6A_Law1479 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1479. -/
theorem noS6A_Law1479 : ∀ v : Magma.tupS6A,
    ¬ @Equation1479 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1479) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1479) (by native_decide) v.1 v.2
    ((@Law1479.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1484 takes them (154 nodes). -/
def ordS6A_Law1484 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1484. -/
theorem noS6A_Law1484 : ∀ v : Magma.tupS6A,
    ¬ @Equation1484 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1484) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1484) (by native_decide) v.1 v.2
    ((@Law1484.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1488 takes them (323 nodes). -/
def ordS6A_Law1488 : List (Fin 11) := [7, 5, 0, 4, 9, 3, 1, 2, 6, 10, 8]

/-- No member of the class satisfies equation 1488. -/
theorem noS6A_Law1488 : ∀ v : Magma.tupS6A,
    ¬ @Equation1488 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1488) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1488) (by native_decide) v.1 v.2
    ((@Law1488.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch6A_refutes_12 :
    FamilyRefutes Magma.srch6A [
      1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475,
      1476, 1477, 1479, 1484, 1488
    ] :=
  ⟨noS6A_Law1461, noS6A_Law1462, noS6A_Law1463, noS6A_Law1464, noS6A_Law1465, noS6A_Law1466, noS6A_Law1467, noS6A_Law1468, noS6A_Law1469, noS6A_Law1470, noS6A_Law1471, noS6A_Law1472, noS6A_Law1473, noS6A_Law1474, noS6A_Law1475, noS6A_Law1476, noS6A_Law1477, noS6A_Law1479, noS6A_Law1484, noS6A_Law1488⟩

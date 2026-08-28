import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 12 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `22`
equations here, 3,117 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1366 takes them (119 nodes). -/
def ordS6A_Law1366 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1366. -/
theorem noS6A_Law1366 : ∀ v : Magma.tupS6A,
    ¬ @Equation1366 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1366) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1366) (by native_decide) v.1 v.2
    ((@Law1366.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (152 nodes). -/
def ordS6A_Law1374 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1374. -/
theorem noS6A_Law1374 : ∀ v : Magma.tupS6A,
    ¬ @Equation1374 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1378 takes them (67 nodes). -/
def ordS6A_Law1378 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1378. -/
theorem noS6A_Law1378 : ∀ v : Magma.tupS6A,
    ¬ @Equation1378 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1378) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1378) (by native_decide) v.1 v.2
    ((@Law1378.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1383 takes them (117 nodes). -/
def ordS6A_Law1383 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1383. -/
theorem noS6A_Law1383 : ∀ v : Magma.tupS6A,
    ¬ @Equation1383 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1383) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1383) (by native_decide) v.1 v.2
    ((@Law1383.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1391 takes them (107 nodes). -/
def ordS6A_Law1391 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1391. -/
theorem noS6A_Law1391 : ∀ v : Magma.tupS6A,
    ¬ @Equation1391 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1391) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1391) (by native_decide) v.1 v.2
    ((@Law1391.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1395 takes them (107 nodes). -/
def ordS6A_Law1395 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1395. -/
theorem noS6A_Law1395 : ∀ v : Magma.tupS6A,
    ¬ @Equation1395 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1395) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1395) (by native_decide) v.1 v.2
    ((@Law1395.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1400 takes them (48 nodes). -/
def ordS6A_Law1400 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1400. -/
theorem noS6A_Law1400 : ∀ v : Magma.tupS6A,
    ¬ @Equation1400 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1400) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1400) (by native_decide) v.1 v.2
    ((@Law1400.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1410 takes them (75 nodes). -/
def ordS6A_Law1410 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1410. -/
theorem noS6A_Law1410 : ∀ v : Magma.tupS6A,
    ¬ @Equation1410 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1410) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1410) (by native_decide) v.1 v.2
    ((@Law1410.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1415 takes them (38 nodes). -/
def ordS6A_Law1415 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1415. -/
theorem noS6A_Law1415 : ∀ v : Magma.tupS6A,
    ¬ @Equation1415 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1415) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1415) (by native_decide) v.1 v.2
    ((@Law1415.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1420 takes them (34 nodes). -/
def ordS6A_Law1420 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1420. -/
theorem noS6A_Law1420 : ∀ v : Magma.tupS6A,
    ¬ @Equation1420 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1420) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1420) (by native_decide) v.1 v.2
    ((@Law1420.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1433 takes them (203 nodes). -/
def ordS6A_Law1433 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1433. -/
theorem noS6A_Law1433 : ∀ v : Magma.tupS6A,
    ¬ @Equation1433 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1433) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1433) (by native_decide) v.1 v.2
    ((@Law1433.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1436 takes them (224 nodes). -/
def ordS6A_Law1436 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1436. -/
theorem noS6A_Law1436 : ∀ v : Magma.tupS6A,
    ¬ @Equation1436 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1436) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1436) (by native_decide) v.1 v.2
    ((@Law1436.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1438 takes them (359 nodes). -/
def ordS6A_Law1438 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1438. -/
theorem noS6A_Law1438 : ∀ v : Magma.tupS6A,
    ¬ @Equation1438 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1438) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1438) (by native_decide) v.1 v.2
    ((@Law1438.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1439 takes them (383 nodes). -/
def ordS6A_Law1439 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1439. -/
theorem noS6A_Law1439 : ∀ v : Magma.tupS6A,
    ¬ @Equation1439 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1439) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1439) (by native_decide) v.1 v.2
    ((@Law1439.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1440 takes them (175 nodes). -/
def ordS6A_Law1440 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1440. -/
theorem noS6A_Law1440 : ∀ v : Magma.tupS6A,
    ¬ @Equation1440 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1440) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1440) (by native_decide) v.1 v.2
    ((@Law1440.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1443 takes them (67 nodes). -/
def ordS6A_Law1443 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1443. -/
theorem noS6A_Law1443 : ∀ v : Magma.tupS6A,
    ¬ @Equation1443 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1443) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1443) (by native_decide) v.1 v.2
    ((@Law1443.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1445 takes them (75 nodes). -/
def ordS6A_Law1445 : List (Fin 11) := [7, 5, 1, 6, 0, 8, 9, 10, 4, 3, 2]

/-- No member of the class satisfies equation 1445. -/
theorem noS6A_Law1445 : ∀ v : Magma.tupS6A,
    ¬ @Equation1445 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1445) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1445) (by native_decide) v.1 v.2
    ((@Law1445.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1446 takes them (132 nodes). -/
def ordS6A_Law1446 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1446. -/
theorem noS6A_Law1446 : ∀ v : Magma.tupS6A,
    ¬ @Equation1446 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1446) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1446) (by native_decide) v.1 v.2
    ((@Law1446.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1447 takes them (373 nodes). -/
def ordS6A_Law1447 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1447. -/
theorem noS6A_Law1447 : ∀ v : Magma.tupS6A,
    ¬ @Equation1447 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1447) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1447) (by native_decide) v.1 v.2
    ((@Law1447.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1448 takes them (106 nodes). -/
def ordS6A_Law1448 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1448. -/
theorem noS6A_Law1448 : ∀ v : Magma.tupS6A,
    ¬ @Equation1448 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1448) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1448) (by native_decide) v.1 v.2
    ((@Law1448.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1449 takes them (98 nodes). -/
def ordS6A_Law1449 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1449. -/
theorem noS6A_Law1449 : ∀ v : Magma.tupS6A,
    ¬ @Equation1449 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1449) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1449) (by native_decide) v.1 v.2
    ((@Law1449.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1450 takes them (58 nodes). -/
def ordS6A_Law1450 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1450. -/
theorem noS6A_Law1450 : ∀ v : Magma.tupS6A,
    ¬ @Equation1450 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1450) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1450) (by native_decide) v.1 v.2
    ((@Law1450.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `22` equations. -/
theorem srch6A_refutes_11 :
    FamilyRefutes Magma.srch6A [
      1366, 1374, 1378, 1383, 1391, 1395, 1400, 1410, 1415, 1420, 1433, 1436, 1438, 1439, 1440,
      1443, 1445, 1446, 1447, 1448, 1449, 1450
    ] :=
  ⟨noS6A_Law1366, noS6A_Law1374, noS6A_Law1378, noS6A_Law1383, noS6A_Law1391, noS6A_Law1395, noS6A_Law1400, noS6A_Law1410, noS6A_Law1415, noS6A_Law1420, noS6A_Law1433, noS6A_Law1436, noS6A_Law1438, noS6A_Law1439, noS6A_Law1440, noS6A_Law1443, noS6A_Law1445, noS6A_Law1446, noS6A_Law1447, noS6A_Law1448, noS6A_Law1449, noS6A_Law1450⟩

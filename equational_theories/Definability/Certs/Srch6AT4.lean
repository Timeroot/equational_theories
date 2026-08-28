import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 5 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `40`
equations here, 2,396 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 403 takes them (148 nodes). -/
def ordS6A_Law403 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 403. -/
theorem noS6A_Law403 : ∀ v : Magma.tupS6A,
    ¬ @Equation403 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law403) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law403) (by native_decide) v.1 v.2
    ((@Law403.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 404 takes them (95 nodes). -/
def ordS6A_Law404 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 404. -/
theorem noS6A_Law404 : ∀ v : Magma.tupS6A,
    ¬ @Equation404 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law404) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law404) (by native_decide) v.1 v.2
    ((@Law404.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 405 takes them (95 nodes). -/
def ordS6A_Law405 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 405. -/
theorem noS6A_Law405 : ∀ v : Magma.tupS6A,
    ¬ @Equation405 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law405) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law405) (by native_decide) v.1 v.2
    ((@Law405.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 406 takes them (24 nodes). -/
def ordS6A_Law406 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 406. -/
theorem noS6A_Law406 : ∀ v : Magma.tupS6A,
    ¬ @Equation406 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law406) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law406) (by native_decide) v.1 v.2
    ((@Law406.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 407 takes them (63 nodes). -/
def ordS6A_Law407 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 407. -/
theorem noS6A_Law407 : ∀ v : Magma.tupS6A,
    ¬ @Equation407 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law407) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law407) (by native_decide) v.1 v.2
    ((@Law407.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 408 takes them (22 nodes). -/
def ordS6A_Law408 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 408. -/
theorem noS6A_Law408 : ∀ v : Magma.tupS6A,
    ¬ @Equation408 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law408) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law408) (by native_decide) v.1 v.2
    ((@Law408.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 409 takes them (22 nodes). -/
def ordS6A_Law409 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 409. -/
theorem noS6A_Law409 : ∀ v : Magma.tupS6A,
    ¬ @Equation409 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law409) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law409) (by native_decide) v.1 v.2
    ((@Law409.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 410 takes them (22 nodes). -/
def ordS6A_Law410 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 410. -/
theorem noS6A_Law410 : ∀ v : Magma.tupS6A,
    ¬ @Equation410 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law410) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law410) (by native_decide) v.1 v.2
    ((@Law410.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 431 takes them (29 nodes). -/
def ordS6A_Law431 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 431. -/
theorem noS6A_Law431 : ∀ v : Magma.tupS6A,
    ¬ @Equation431 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law431) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law431) (by native_decide) v.1 v.2
    ((@Law431.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 435 takes them (27 nodes). -/
def ordS6A_Law435 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 435. -/
theorem noS6A_Law435 : ∀ v : Magma.tupS6A,
    ¬ @Equation435 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law435) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law435) (by native_decide) v.1 v.2
    ((@Law435.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 438 takes them (34 nodes). -/
def ordS6A_Law438 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 438. -/
theorem noS6A_Law438 : ∀ v : Magma.tupS6A,
    ¬ @Equation438 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law438) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law438) (by native_decide) v.1 v.2
    ((@Law438.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 441 takes them (35 nodes). -/
def ordS6A_Law441 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 441. -/
theorem noS6A_Law441 : ∀ v : Magma.tupS6A,
    ¬ @Equation441 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law441) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law441) (by native_decide) v.1 v.2
    ((@Law441.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 445 takes them (31 nodes). -/
def ordS6A_Law445 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 445. -/
theorem noS6A_Law445 : ∀ v : Magma.tupS6A,
    ¬ @Equation445 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law445) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law445) (by native_decide) v.1 v.2
    ((@Law445.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 447 takes them (77 nodes). -/
def ordS6A_Law447 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 447. -/
theorem noS6A_Law447 : ∀ v : Magma.tupS6A,
    ¬ @Equation447 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law447) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law447) (by native_decide) v.1 v.2
    ((@Law447.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 448 takes them (69 nodes). -/
def ordS6A_Law448 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 448. -/
theorem noS6A_Law448 : ∀ v : Magma.tupS6A,
    ¬ @Equation448 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law448) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law448) (by native_decide) v.1 v.2
    ((@Law448.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 449 takes them (27 nodes). -/
def ordS6A_Law449 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 449. -/
theorem noS6A_Law449 : ∀ v : Magma.tupS6A,
    ¬ @Equation449 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law449) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law449) (by native_decide) v.1 v.2
    ((@Law449.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 451 takes them (95 nodes). -/
def ordS6A_Law451 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 451. -/
theorem noS6A_Law451 : ∀ v : Magma.tupS6A,
    ¬ @Equation451 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law451) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law451) (by native_decide) v.1 v.2
    ((@Law451.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 453 takes them (26 nodes). -/
def ordS6A_Law453 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 453. -/
theorem noS6A_Law453 : ∀ v : Magma.tupS6A,
    ¬ @Equation453 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law453) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law453) (by native_decide) v.1 v.2
    ((@Law453.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 456 takes them (73 nodes). -/
def ordS6A_Law456 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 456. -/
theorem noS6A_Law456 : ∀ v : Magma.tupS6A,
    ¬ @Equation456 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law456) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law456) (by native_decide) v.1 v.2
    ((@Law456.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 457 takes them (25 nodes). -/
def ordS6A_Law457 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 457. -/
theorem noS6A_Law457 : ∀ v : Magma.tupS6A,
    ¬ @Equation457 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law457) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law457) (by native_decide) v.1 v.2
    ((@Law457.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 459 takes them (73 nodes). -/
def ordS6A_Law459 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 459. -/
theorem noS6A_Law459 : ∀ v : Magma.tupS6A,
    ¬ @Equation459 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law459) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law459) (by native_decide) v.1 v.2
    ((@Law459.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 460 takes them (65 nodes). -/
def ordS6A_Law460 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 460. -/
theorem noS6A_Law460 : ∀ v : Magma.tupS6A,
    ¬ @Equation460 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law460) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law460) (by native_decide) v.1 v.2
    ((@Law460.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 461 takes them (73 nodes). -/
def ordS6A_Law461 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 461. -/
theorem noS6A_Law461 : ∀ v : Magma.tupS6A,
    ¬ @Equation461 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law461) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law461) (by native_decide) v.1 v.2
    ((@Law461.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 462 takes them (25 nodes). -/
def ordS6A_Law462 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 462. -/
theorem noS6A_Law462 : ∀ v : Magma.tupS6A,
    ¬ @Equation462 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law462) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law462) (by native_decide) v.1 v.2
    ((@Law462.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 463 takes them (112 nodes). -/
def ordS6A_Law463 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 463. -/
theorem noS6A_Law463 : ∀ v : Magma.tupS6A,
    ¬ @Equation463 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law463) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law463) (by native_decide) v.1 v.2
    ((@Law463.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 469 takes them (69 nodes). -/
def ordS6A_Law469 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 469. -/
theorem noS6A_Law469 : ∀ v : Magma.tupS6A,
    ¬ @Equation469 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law469) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law469) (by native_decide) v.1 v.2
    ((@Law469.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 479 takes them (73 nodes). -/
def ordS6A_Law479 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 479. -/
theorem noS6A_Law479 : ∀ v : Magma.tupS6A,
    ¬ @Equation479 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law479) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law479) (by native_decide) v.1 v.2
    ((@Law479.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 483 takes them (95 nodes). -/
def ordS6A_Law483 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 483. -/
theorem noS6A_Law483 : ∀ v : Magma.tupS6A,
    ¬ @Equation483 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law483) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law483) (by native_decide) v.1 v.2
    ((@Law483.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 487 takes them (73 nodes). -/
def ordS6A_Law487 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 487. -/
theorem noS6A_Law487 : ∀ v : Magma.tupS6A,
    ¬ @Equation487 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law487) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law487) (by native_decide) v.1 v.2
    ((@Law487.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 491 takes them (66 nodes). -/
def ordS6A_Law491 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 491. -/
theorem noS6A_Law491 : ∀ v : Magma.tupS6A,
    ¬ @Equation491 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law491) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law491) (by native_decide) v.1 v.2
    ((@Law491.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 495 takes them (66 nodes). -/
def ordS6A_Law495 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 495. -/
theorem noS6A_Law495 : ∀ v : Magma.tupS6A,
    ¬ @Equation495 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law495) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law495) (by native_decide) v.1 v.2
    ((@Law495.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 506 takes them (76 nodes). -/
def ordS6A_Law506 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 506. -/
theorem noS6A_Law506 : ∀ v : Magma.tupS6A,
    ¬ @Equation506 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law506) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law506) (by native_decide) v.1 v.2
    ((@Law506.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 516 takes them (23 nodes). -/
def ordS6A_Law516 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 516. -/
theorem noS6A_Law516 : ∀ v : Magma.tupS6A,
    ¬ @Equation516 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law516) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law516) (by native_decide) v.1 v.2
    ((@Law516.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 520 takes them (101 nodes). -/
def ordS6A_Law520 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 520. -/
theorem noS6A_Law520 : ∀ v : Magma.tupS6A,
    ¬ @Equation520 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law520) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law520) (by native_decide) v.1 v.2
    ((@Law520.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 524 takes them (26 nodes). -/
def ordS6A_Law524 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 524. -/
theorem noS6A_Law524 : ∀ v : Magma.tupS6A,
    ¬ @Equation524 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law524) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law524) (by native_decide) v.1 v.2
    ((@Law524.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 532 takes them (23 nodes). -/
def ordS6A_Law532 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 532. -/
theorem noS6A_Law532 : ∀ v : Magma.tupS6A,
    ¬ @Equation532 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law532) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law532) (by native_decide) v.1 v.2
    ((@Law532.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 537 takes them (112 nodes). -/
def ordS6A_Law537 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 537. -/
theorem noS6A_Law537 : ∀ v : Magma.tupS6A,
    ¬ @Equation537 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law537) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law537) (by native_decide) v.1 v.2
    ((@Law537.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 541 takes them (74 nodes). -/
def ordS6A_Law541 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 541. -/
theorem noS6A_Law541 : ∀ v : Magma.tupS6A,
    ¬ @Equation541 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law541) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law541) (by native_decide) v.1 v.2
    ((@Law541.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 545 takes them (66 nodes). -/
def ordS6A_Law545 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 545. -/
theorem noS6A_Law545 : ∀ v : Magma.tupS6A,
    ¬ @Equation545 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law545) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law545) (by native_decide) v.1 v.2
    ((@Law545.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 549 takes them (66 nodes). -/
def ordS6A_Law549 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 549. -/
theorem noS6A_Law549 : ∀ v : Magma.tupS6A,
    ¬ @Equation549 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law549) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law549) (by native_decide) v.1 v.2
    ((@Law549.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `40` equations. -/
theorem srch6A_refutes_4 :
    FamilyRefutes Magma.srch6A [
      403, 404, 405, 406, 407, 408, 409, 410, 431, 435, 438, 441, 445, 447, 448, 449, 451, 453,
      456, 457, 459, 460, 461, 462, 463, 469, 479, 483, 487, 491, 495, 506, 516, 520, 524, 532,
      537, 541, 545, 549
    ] :=
  ⟨noS6A_Law403, noS6A_Law404, noS6A_Law405, noS6A_Law406, noS6A_Law407, noS6A_Law408, noS6A_Law409, noS6A_Law410, noS6A_Law431, noS6A_Law435, noS6A_Law438, noS6A_Law441, noS6A_Law445, noS6A_Law447, noS6A_Law448, noS6A_Law449, noS6A_Law451, noS6A_Law453, noS6A_Law456, noS6A_Law457, noS6A_Law459, noS6A_Law460, noS6A_Law461, noS6A_Law462, noS6A_Law463, noS6A_Law469, noS6A_Law479, noS6A_Law483, noS6A_Law487, noS6A_Law491, noS6A_Law495, noS6A_Law506, noS6A_Law516, noS6A_Law520, noS6A_Law524, noS6A_Law532, noS6A_Law537, noS6A_Law541, noS6A_Law545, noS6A_Law549⟩

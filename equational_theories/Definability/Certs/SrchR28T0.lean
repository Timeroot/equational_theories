import equational_theories.Definability.Srch_SR28

/-!
# Structural certificate targets: `Magma.srchR28`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR28_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `35`
equations here, 1,042 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR28_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4407 takes them (39 nodes). -/
def ordSR28_Law4407 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4407. -/
theorem noSR28_Law4407 : ∀ v : Magma.tupR28,
    ¬ @Equation4407 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4407) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4407) (by native_decide) v.1 v.2
    ((@Law4407.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4411 takes them (42 nodes). -/
def ordSR28_Law4411 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4411. -/
theorem noSR28_Law4411 : ∀ v : Magma.tupR28,
    ¬ @Equation4411 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4411) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4411) (by native_decide) v.1 v.2
    ((@Law4411.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4414 takes them (18 nodes). -/
def ordSR28_Law4414 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4414. -/
theorem noSR28_Law4414 : ∀ v : Magma.tupR28,
    ¬ @Equation4414 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4414) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4414) (by native_decide) v.1 v.2
    ((@Law4414.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4418 takes them (35 nodes). -/
def ordSR28_Law4418 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4418. -/
theorem noSR28_Law4418 : ∀ v : Magma.tupR28,
    ¬ @Equation4418 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4418) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4418) (by native_decide) v.1 v.2
    ((@Law4418.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4419 takes them (46 nodes). -/
def ordSR28_Law4419 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4419. -/
theorem noSR28_Law4419 : ∀ v : Magma.tupR28,
    ¬ @Equation4419 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4419) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4419) (by native_decide) v.1 v.2
    ((@Law4419.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4422 takes them (17 nodes). -/
def ordSR28_Law4422 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4422. -/
theorem noSR28_Law4422 : ∀ v : Magma.tupR28,
    ¬ @Equation4422 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4422) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4422) (by native_decide) v.1 v.2
    ((@Law4422.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4427 takes them (25 nodes). -/
def ordSR28_Law4427 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4427. -/
theorem noSR28_Law4427 : ∀ v : Magma.tupR28,
    ¬ @Equation4427 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4427) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4427) (by native_decide) v.1 v.2
    ((@Law4427.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4431 takes them (14 nodes). -/
def ordSR28_Law4431 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4431. -/
theorem noSR28_Law4431 : ∀ v : Magma.tupR28,
    ¬ @Equation4431 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4431) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4431) (by native_decide) v.1 v.2
    ((@Law4431.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4523 takes them (51 nodes). -/
def ordSR28_Law4523 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4523. -/
theorem noSR28_Law4523 : ∀ v : Magma.tupR28,
    ¬ @Equation4523 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4523) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4523) (by native_decide) v.1 v.2
    ((@Law4523.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4526 takes them (37 nodes). -/
def ordSR28_Law4526 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4526. -/
theorem noSR28_Law4526 : ∀ v : Magma.tupR28,
    ¬ @Equation4526 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4526) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4526) (by native_decide) v.1 v.2
    ((@Law4526.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4534 takes them (18 nodes). -/
def ordSR28_Law4534 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4534. -/
theorem noSR28_Law4534 : ∀ v : Magma.tupR28,
    ¬ @Equation4534 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4534) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4534) (by native_decide) v.1 v.2
    ((@Law4534.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4535 takes them (25 nodes). -/
def ordSR28_Law4535 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4535. -/
theorem noSR28_Law4535 : ∀ v : Magma.tupR28,
    ¬ @Equation4535 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4535) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4535) (by native_decide) v.1 v.2
    ((@Law4535.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4538 takes them (15 nodes). -/
def ordSR28_Law4538 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4538. -/
theorem noSR28_Law4538 : ∀ v : Magma.tupR28,
    ¬ @Equation4538 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4538) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4538) (by native_decide) v.1 v.2
    ((@Law4538.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4539 takes them (15 nodes). -/
def ordSR28_Law4539 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4539. -/
theorem noSR28_Law4539 : ∀ v : Magma.tupR28,
    ¬ @Equation4539 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4539) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4539) (by native_decide) v.1 v.2
    ((@Law4539.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4540 takes them (59 nodes). -/
def ordSR28_Law4540 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4540. -/
theorem noSR28_Law4540 : ∀ v : Magma.tupR28,
    ¬ @Equation4540 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4540) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4540) (by native_decide) v.1 v.2
    ((@Law4540.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4543 takes them (38 nodes). -/
def ordSR28_Law4543 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4543. -/
theorem noSR28_Law4543 : ∀ v : Magma.tupR28,
    ¬ @Equation4543 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4543) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4543) (by native_decide) v.1 v.2
    ((@Law4543.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4545 takes them (41 nodes). -/
def ordSR28_Law4545 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4545. -/
theorem noSR28_Law4545 : ∀ v : Magma.tupR28,
    ¬ @Equation4545 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4545) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 3)
    (ord := ordSR28_Law4545) (by native_decide) v.1 v.2
    ((@Law4545.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4547 takes them (36 nodes). -/
def ordSR28_Law4547 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4547. -/
theorem noSR28_Law4547 : ∀ v : Magma.tupR28,
    ¬ @Equation4547 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4547) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4547) (by native_decide) v.1 v.2
    ((@Law4547.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4552 takes them (34 nodes). -/
def ordSR28_Law4552 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4552. -/
theorem noSR28_Law4552 : ∀ v : Magma.tupR28,
    ¬ @Equation4552 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4552) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4552) (by native_decide) v.1 v.2
    ((@Law4552.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4553 takes them (30 nodes). -/
def ordSR28_Law4553 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4553. -/
theorem noSR28_Law4553 : ∀ v : Magma.tupR28,
    ¬ @Equation4553 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4553) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4553) (by native_decide) v.1 v.2
    ((@Law4553.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4555 takes them (19 nodes). -/
def ordSR28_Law4555 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4555. -/
theorem noSR28_Law4555 : ∀ v : Magma.tupR28,
    ¬ @Equation4555 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4555) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4555) (by native_decide) v.1 v.2
    ((@Law4555.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4556 takes them (18 nodes). -/
def ordSR28_Law4556 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4556. -/
theorem noSR28_Law4556 : ∀ v : Magma.tupR28,
    ¬ @Equation4556 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4556) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4556) (by native_decide) v.1 v.2
    ((@Law4556.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4557 takes them (33 nodes). -/
def ordSR28_Law4557 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4557. -/
theorem noSR28_Law4557 : ∀ v : Magma.tupR28,
    ¬ @Equation4557 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4557) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4557) (by native_decide) v.1 v.2
    ((@Law4557.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4558 takes them (35 nodes). -/
def ordSR28_Law4558 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4558. -/
theorem noSR28_Law4558 : ∀ v : Magma.tupR28,
    ¬ @Equation4558 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4558) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4558) (by native_decide) v.1 v.2
    ((@Law4558.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4561 takes them (32 nodes). -/
def ordSR28_Law4561 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4561. -/
theorem noSR28_Law4561 : ∀ v : Magma.tupR28,
    ¬ @Equation4561 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4561) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4561) (by native_decide) v.1 v.2
    ((@Law4561.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4562 takes them (37 nodes). -/
def ordSR28_Law4562 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4562. -/
theorem noSR28_Law4562 : ∀ v : Magma.tupR28,
    ¬ @Equation4562 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4562) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4562) (by native_decide) v.1 v.2
    ((@Law4562.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4563 takes them (33 nodes). -/
def ordSR28_Law4563 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4563. -/
theorem noSR28_Law4563 : ∀ v : Magma.tupR28,
    ¬ @Equation4563 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4563) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4563) (by native_decide) v.1 v.2
    ((@Law4563.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4566 takes them (33 nodes). -/
def ordSR28_Law4566 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4566. -/
theorem noSR28_Law4566 : ∀ v : Magma.tupR28,
    ¬ @Equation4566 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4566) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4566) (by native_decide) v.1 v.2
    ((@Law4566.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4567 takes them (38 nodes). -/
def ordSR28_Law4567 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4567. -/
theorem noSR28_Law4567 : ∀ v : Magma.tupR28,
    ¬ @Equation4567 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4567) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4567) (by native_decide) v.1 v.2
    ((@Law4567.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4568 takes them (40 nodes). -/
def ordSR28_Law4568 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4568. -/
theorem noSR28_Law4568 : ∀ v : Magma.tupR28,
    ¬ @Equation4568 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4568) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 4)
    (ord := ordSR28_Law4568) (by native_decide) v.1 v.2
    ((@Law4568.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4571 takes them (17 nodes). -/
def ordSR28_Law4571 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4571. -/
theorem noSR28_Law4571 : ∀ v : Magma.tupR28,
    ¬ @Equation4571 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4571) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4571) (by native_decide) v.1 v.2
    ((@Law4571.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4577 takes them (23 nodes). -/
def ordSR28_Law4577 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4577. -/
theorem noSR28_Law4577 : ∀ v : Magma.tupR28,
    ¬ @Equation4577 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4577) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4577) (by native_decide) v.1 v.2
    ((@Law4577.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4578 takes them (22 nodes). -/
def ordSR28_Law4578 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4578. -/
theorem noSR28_Law4578 : ∀ v : Magma.tupR28,
    ¬ @Equation4578 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4578) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4578) (by native_decide) v.1 v.2
    ((@Law4578.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4581 takes them (14 nodes). -/
def ordSR28_Law4581 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4581. -/
theorem noSR28_Law4581 : ∀ v : Magma.tupR28,
    ¬ @Equation4581 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4581) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 5)
    (ord := ordSR28_Law4581) (by native_decide) v.1 v.2
    ((@Law4581.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4582 takes them (13 nodes). -/
def ordSR28_Law4582 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4582. -/
theorem noSR28_Law4582 : ∀ v : Magma.tupR28,
    ¬ @Equation4582 (Fin 6) (Magma.srchR28 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4582) (E := SR28.E) (tr := SR28.tr) (z := SR28.z)
    (st := SR28.st) (X := SR28.X) (envs := Magma.envsRed 6 SR28.E 6)
    (ord := ordSR28_Law4582) (by native_decide) v.1 v.2
    ((@Law4582.models_iff (Fin 6) (Magma.srchR28 v)).mpr hv)

/-- No member of the class satisfies any of these `35` equations. -/
theorem srchR28_refutes_0 :
    FamilyRefutes Magma.srchR28 [
      4407, 4411, 4414, 4418, 4419, 4422, 4427, 4431, 4523, 4526, 4534, 4535, 4538, 4539, 4540,
      4543, 4545, 4547, 4552, 4553, 4555, 4556, 4557, 4558, 4561, 4562, 4563, 4566, 4567, 4568,
      4571, 4577, 4578, 4581, 4582
    ] :=
  ⟨noSR28_Law4407, noSR28_Law4411, noSR28_Law4414, noSR28_Law4418, noSR28_Law4419, noSR28_Law4422, noSR28_Law4427, noSR28_Law4431, noSR28_Law4523, noSR28_Law4526, noSR28_Law4534, noSR28_Law4535, noSR28_Law4538, noSR28_Law4539, noSR28_Law4540, noSR28_Law4543, noSR28_Law4545, noSR28_Law4547, noSR28_Law4552, noSR28_Law4553, noSR28_Law4555, noSR28_Law4556, noSR28_Law4557, noSR28_Law4558, noSR28_Law4561, noSR28_Law4562, noSR28_Law4563, noSR28_Law4566, noSR28_Law4567, noSR28_Law4568, noSR28_Law4571, noSR28_Law4577, noSR28_Law4578, noSR28_Law4581, noSR28_Law4582⟩

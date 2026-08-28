import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 2 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 307 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 442 takes them (4 nodes). -/
def ordS11R173_Law442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 442. -/
theorem noS11R173_Law442 : ∀ v : Magma.tup11R173,
    ¬ @Equation442 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law442) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law442) (by native_decide) v.1 v.2
    ((@Law442.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 446 takes them (4 nodes). -/
def ordS11R173_Law446 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 446. -/
theorem noS11R173_Law446 : ∀ v : Magma.tup11R173,
    ¬ @Equation446 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law446) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law446) (by native_decide) v.1 v.2
    ((@Law446.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 450 takes them (4 nodes). -/
def ordS11R173_Law450 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 450. -/
theorem noS11R173_Law450 : ∀ v : Magma.tup11R173,
    ¬ @Equation450 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law450) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law450) (by native_decide) v.1 v.2
    ((@Law450.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 454 takes them (4 nodes). -/
def ordS11R173_Law454 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 454. -/
theorem noS11R173_Law454 : ∀ v : Magma.tup11R173,
    ¬ @Equation454 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law454) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law454) (by native_decide) v.1 v.2
    ((@Law454.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 458 takes them (4 nodes). -/
def ordS11R173_Law458 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 458. -/
theorem noS11R173_Law458 : ∀ v : Magma.tup11R173,
    ¬ @Equation458 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law458) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law458) (by native_decide) v.1 v.2
    ((@Law458.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 463 takes them (3 nodes). -/
def ordS11R173_Law463 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 463. -/
theorem noS11R173_Law463 : ∀ v : Magma.tup11R173,
    ¬ @Equation463 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law463) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law463) (by native_decide) v.1 v.2
    ((@Law463.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 469 takes them (3 nodes). -/
def ordS11R173_Law469 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 469. -/
theorem noS11R173_Law469 : ∀ v : Magma.tup11R173,
    ¬ @Equation469 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law469) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law469) (by native_decide) v.1 v.2
    ((@Law469.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (3 nodes). -/
def ordS11R173_Law473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 473. -/
theorem noS11R173_Law473 : ∀ v : Magma.tup11R173,
    ¬ @Equation473 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 479 takes them (3 nodes). -/
def ordS11R173_Law479 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 479. -/
theorem noS11R173_Law479 : ∀ v : Magma.tup11R173,
    ¬ @Equation479 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law479) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law479) (by native_decide) v.1 v.2
    ((@Law479.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 483 takes them (3 nodes). -/
def ordS11R173_Law483 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 483. -/
theorem noS11R173_Law483 : ∀ v : Magma.tup11R173,
    ¬ @Equation483 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law483) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law483) (by native_decide) v.1 v.2
    ((@Law483.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 487 takes them (3 nodes). -/
def ordS11R173_Law487 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 487. -/
theorem noS11R173_Law487 : ∀ v : Magma.tup11R173,
    ¬ @Equation487 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law487) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law487) (by native_decide) v.1 v.2
    ((@Law487.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 491 takes them (3 nodes). -/
def ordS11R173_Law491 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 491. -/
theorem noS11R173_Law491 : ∀ v : Magma.tup11R173,
    ¬ @Equation491 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law491) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law491) (by native_decide) v.1 v.2
    ((@Law491.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 495 takes them (3 nodes). -/
def ordS11R173_Law495 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 495. -/
theorem noS11R173_Law495 : ∀ v : Magma.tup11R173,
    ¬ @Equation495 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law495) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law495) (by native_decide) v.1 v.2
    ((@Law495.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 506 takes them (3 nodes). -/
def ordS11R173_Law506 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 506. -/
theorem noS11R173_Law506 : ∀ v : Magma.tup11R173,
    ¬ @Equation506 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law506) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law506) (by native_decide) v.1 v.2
    ((@Law506.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 510 takes them (3 nodes). -/
def ordS11R173_Law510 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 510. -/
theorem noS11R173_Law510 : ∀ v : Magma.tup11R173,
    ¬ @Equation510 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law510) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law510) (by native_decide) v.1 v.2
    ((@Law510.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 516 takes them (3 nodes). -/
def ordS11R173_Law516 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 516. -/
theorem noS11R173_Law516 : ∀ v : Magma.tup11R173,
    ¬ @Equation516 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law516) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law516) (by native_decide) v.1 v.2
    ((@Law516.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 520 takes them (3 nodes). -/
def ordS11R173_Law520 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 520. -/
theorem noS11R173_Law520 : ∀ v : Magma.tup11R173,
    ¬ @Equation520 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law520) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law520) (by native_decide) v.1 v.2
    ((@Law520.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 524 takes them (3 nodes). -/
def ordS11R173_Law524 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 524. -/
theorem noS11R173_Law524 : ∀ v : Magma.tup11R173,
    ¬ @Equation524 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law524) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law524) (by native_decide) v.1 v.2
    ((@Law524.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 532 takes them (3 nodes). -/
def ordS11R173_Law532 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 532. -/
theorem noS11R173_Law532 : ∀ v : Magma.tup11R173,
    ¬ @Equation532 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law532) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law532) (by native_decide) v.1 v.2
    ((@Law532.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 537 takes them (3 nodes). -/
def ordS11R173_Law537 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 537. -/
theorem noS11R173_Law537 : ∀ v : Magma.tup11R173,
    ¬ @Equation537 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law537) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law537) (by native_decide) v.1 v.2
    ((@Law537.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 541 takes them (3 nodes). -/
def ordS11R173_Law541 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 541. -/
theorem noS11R173_Law541 : ∀ v : Magma.tup11R173,
    ¬ @Equation541 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law541) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law541) (by native_decide) v.1 v.2
    ((@Law541.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 545 takes them (3 nodes). -/
def ordS11R173_Law545 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 545. -/
theorem noS11R173_Law545 : ∀ v : Magma.tup11R173,
    ¬ @Equation545 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law545) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law545) (by native_decide) v.1 v.2
    ((@Law545.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 549 takes them (3 nodes). -/
def ordS11R173_Law549 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 549. -/
theorem noS11R173_Law549 : ∀ v : Magma.tup11R173,
    ¬ @Equation549 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law549) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law549) (by native_decide) v.1 v.2
    ((@Law549.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 554 takes them (3 nodes). -/
def ordS11R173_Law554 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 554. -/
theorem noS11R173_Law554 : ∀ v : Magma.tup11R173,
    ¬ @Equation554 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law554) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law554) (by native_decide) v.1 v.2
    ((@Law554.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 558 takes them (3 nodes). -/
def ordS11R173_Law558 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 558. -/
theorem noS11R173_Law558 : ∀ v : Magma.tup11R173,
    ¬ @Equation558 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law558) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law558) (by native_decide) v.1 v.2
    ((@Law558.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (3 nodes). -/
def ordS11R173_Law562 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 562. -/
theorem noS11R173_Law562 : ∀ v : Magma.tup11R173,
    ¬ @Equation562 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 566 takes them (3 nodes). -/
def ordS11R173_Law566 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 566. -/
theorem noS11R173_Law566 : ∀ v : Magma.tup11R173,
    ¬ @Equation566 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law566) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law566) (by native_decide) v.1 v.2
    ((@Law566.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 571 takes them (3 nodes). -/
def ordS11R173_Law571 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 571. -/
theorem noS11R173_Law571 : ∀ v : Magma.tup11R173,
    ¬ @Equation571 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law571) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law571) (by native_decide) v.1 v.2
    ((@Law571.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 579 takes them (3 nodes). -/
def ordS11R173_Law579 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 579. -/
theorem noS11R173_Law579 : ∀ v : Magma.tup11R173,
    ¬ @Equation579 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law579) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law579) (by native_decide) v.1 v.2
    ((@Law579.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 583 takes them (3 nodes). -/
def ordS11R173_Law583 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 583. -/
theorem noS11R173_Law583 : ∀ v : Magma.tup11R173,
    ¬ @Equation583 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law583) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law583) (by native_decide) v.1 v.2
    ((@Law583.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 588 takes them (3 nodes). -/
def ordS11R173_Law588 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 588. -/
theorem noS11R173_Law588 : ∀ v : Magma.tup11R173,
    ¬ @Equation588 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law588) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law588) (by native_decide) v.1 v.2
    ((@Law588.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 593 takes them (3 nodes). -/
def ordS11R173_Law593 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 593. -/
theorem noS11R173_Law593 : ∀ v : Magma.tup11R173,
    ¬ @Equation593 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law593) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law593) (by native_decide) v.1 v.2
    ((@Law593.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 598 takes them (3 nodes). -/
def ordS11R173_Law598 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 598. -/
theorem noS11R173_Law598 : ∀ v : Magma.tup11R173,
    ¬ @Equation598 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law598) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law598) (by native_decide) v.1 v.2
    ((@Law598.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 603 takes them (3 nodes). -/
def ordS11R173_Law603 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 603. -/
theorem noS11R173_Law603 : ∀ v : Magma.tup11R173,
    ¬ @Equation603 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law603) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law603) (by native_decide) v.1 v.2
    ((@Law603.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 615 takes them (3 nodes). -/
def ordS11R173_Law615 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 615. -/
theorem noS11R173_Law615 : ∀ v : Magma.tup11R173,
    ¬ @Equation615 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law615) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law615) (by native_decide) v.1 v.2
    ((@Law615.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 616 takes them (4 nodes). -/
def ordS11R173_Law616 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 616. -/
theorem noS11R173_Law616 : ∀ v : Magma.tup11R173,
    ¬ @Equation616 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law616) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law616) (by native_decide) v.1 v.2
    ((@Law616.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 618 takes them (3 nodes). -/
def ordS11R173_Law618 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 618. -/
theorem noS11R173_Law618 : ∀ v : Magma.tup11R173,
    ¬ @Equation618 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law618) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law618) (by native_decide) v.1 v.2
    ((@Law618.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 619 takes them (4 nodes). -/
def ordS11R173_Law619 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 619. -/
theorem noS11R173_Law619 : ∀ v : Magma.tup11R173,
    ¬ @Equation619 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law619) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law619) (by native_decide) v.1 v.2
    ((@Law619.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (3 nodes). -/
def ordS11R173_Law620 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 620. -/
theorem noS11R173_Law620 : ∀ v : Magma.tup11R173,
    ¬ @Equation620 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 621 takes them (3 nodes). -/
def ordS11R173_Law621 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 621. -/
theorem noS11R173_Law621 : ∀ v : Magma.tup11R173,
    ¬ @Equation621 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law621) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law621) (by native_decide) v.1 v.2
    ((@Law621.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 622 takes them (4 nodes). -/
def ordS11R173_Law622 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 622. -/
theorem noS11R173_Law622 : ∀ v : Magma.tup11R173,
    ¬ @Equation622 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law622) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law622) (by native_decide) v.1 v.2
    ((@Law622.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 623 takes them (3 nodes). -/
def ordS11R173_Law623 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 623. -/
theorem noS11R173_Law623 : ∀ v : Magma.tup11R173,
    ¬ @Equation623 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law623) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law623) (by native_decide) v.1 v.2
    ((@Law623.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 624 takes them (3 nodes). -/
def ordS11R173_Law624 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 624. -/
theorem noS11R173_Law624 : ∀ v : Magma.tup11R173,
    ¬ @Equation624 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law624) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law624) (by native_decide) v.1 v.2
    ((@Law624.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 625 takes them (4 nodes). -/
def ordS11R173_Law625 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 625. -/
theorem noS11R173_Law625 : ∀ v : Magma.tup11R173,
    ¬ @Equation625 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law625) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law625) (by native_decide) v.1 v.2
    ((@Law625.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 626 takes them (3 nodes). -/
def ordS11R173_Law626 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 626. -/
theorem noS11R173_Law626 : ∀ v : Magma.tup11R173,
    ¬ @Equation626 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law626) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law626) (by native_decide) v.1 v.2
    ((@Law626.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 627 takes them (3 nodes). -/
def ordS11R173_Law627 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 627. -/
theorem noS11R173_Law627 : ∀ v : Magma.tup11R173,
    ¬ @Equation627 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law627) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law627) (by native_decide) v.1 v.2
    ((@Law627.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 628 takes them (3 nodes). -/
def ordS11R173_Law628 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 628. -/
theorem noS11R173_Law628 : ∀ v : Magma.tup11R173,
    ¬ @Equation628 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law628) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law628) (by native_decide) v.1 v.2
    ((@Law628.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 629 takes them (4 nodes). -/
def ordS11R173_Law629 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 629. -/
theorem noS11R173_Law629 : ∀ v : Magma.tup11R173,
    ¬ @Equation629 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law629) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law629) (by native_decide) v.1 v.2
    ((@Law629.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 632 takes them (4 nodes). -/
def ordS11R173_Law632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 632. -/
theorem noS11R173_Law632 : ∀ v : Magma.tup11R173,
    ¬ @Equation632 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law632) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law632) (by native_decide) v.1 v.2
    ((@Law632.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 635 takes them (4 nodes). -/
def ordS11R173_Law635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 635. -/
theorem noS11R173_Law635 : ∀ v : Magma.tup11R173,
    ¬ @Equation635 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law635) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law635) (by native_decide) v.1 v.2
    ((@Law635.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 645 takes them (4 nodes). -/
def ordS11R173_Law645 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 645. -/
theorem noS11R173_Law645 : ∀ v : Magma.tup11R173,
    ¬ @Equation645 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law645) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law645) (by native_decide) v.1 v.2
    ((@Law645.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 649 takes them (4 nodes). -/
def ordS11R173_Law649 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 649. -/
theorem noS11R173_Law649 : ∀ v : Magma.tup11R173,
    ¬ @Equation649 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law649) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law649) (by native_decide) v.1 v.2
    ((@Law649.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 653 takes them (4 nodes). -/
def ordS11R173_Law653 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 653. -/
theorem noS11R173_Law653 : ∀ v : Magma.tup11R173,
    ¬ @Equation653 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law653) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law653) (by native_decide) v.1 v.2
    ((@Law653.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 657 takes them (4 nodes). -/
def ordS11R173_Law657 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 657. -/
theorem noS11R173_Law657 : ∀ v : Magma.tup11R173,
    ¬ @Equation657 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law657) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law657) (by native_decide) v.1 v.2
    ((@Law657.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 661 takes them (4 nodes). -/
def ordS11R173_Law661 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 661. -/
theorem noS11R173_Law661 : ∀ v : Magma.tup11R173,
    ¬ @Equation661 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law661) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law661) (by native_decide) v.1 v.2
    ((@Law661.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 679 takes them (3 nodes). -/
def ordS11R173_Law679 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 679. -/
theorem noS11R173_Law679 : ∀ v : Magma.tup11R173,
    ¬ @Equation679 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law679) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law679) (by native_decide) v.1 v.2
    ((@Law679.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (3 nodes). -/
def ordS11R173_Law716 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 716. -/
theorem noS11R173_Law716 : ∀ v : Magma.tup11R173,
    ¬ @Equation716 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 818 takes them (3 nodes). -/
def ordS11R173_Law818 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 818. -/
theorem noS11R173_Law818 : ∀ v : Magma.tup11R173,
    ¬ @Equation818 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law818) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law818) (by native_decide) v.1 v.2
    ((@Law818.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 819 takes them (4 nodes). -/
def ordS11R173_Law819 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 819. -/
theorem noS11R173_Law819 : ∀ v : Magma.tup11R173,
    ¬ @Equation819 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law819) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law819) (by native_decide) v.1 v.2
    ((@Law819.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 820 takes them (3 nodes). -/
def ordS11R173_Law820 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 820. -/
theorem noS11R173_Law820 : ∀ v : Magma.tup11R173,
    ¬ @Equation820 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law820) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law820) (by native_decide) v.1 v.2
    ((@Law820.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 821 takes them (3 nodes). -/
def ordS11R173_Law821 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 821. -/
theorem noS11R173_Law821 : ∀ v : Magma.tup11R173,
    ¬ @Equation821 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law821) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law821) (by native_decide) v.1 v.2
    ((@Law821.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 822 takes them (4 nodes). -/
def ordS11R173_Law822 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 822. -/
theorem noS11R173_Law822 : ∀ v : Magma.tup11R173,
    ¬ @Equation822 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law822) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law822) (by native_decide) v.1 v.2
    ((@Law822.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 823 takes them (3 nodes). -/
def ordS11R173_Law823 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 823. -/
theorem noS11R173_Law823 : ∀ v : Magma.tup11R173,
    ¬ @Equation823 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law823) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law823) (by native_decide) v.1 v.2
    ((@Law823.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 824 takes them (3 nodes). -/
def ordS11R173_Law824 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 824. -/
theorem noS11R173_Law824 : ∀ v : Magma.tup11R173,
    ¬ @Equation824 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law824) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law824) (by native_decide) v.1 v.2
    ((@Law824.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 825 takes them (4 nodes). -/
def ordS11R173_Law825 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 825. -/
theorem noS11R173_Law825 : ∀ v : Magma.tup11R173,
    ¬ @Equation825 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law825) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law825) (by native_decide) v.1 v.2
    ((@Law825.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 827 takes them (3 nodes). -/
def ordS11R173_Law827 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 827. -/
theorem noS11R173_Law827 : ∀ v : Magma.tup11R173,
    ¬ @Equation827 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law827) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law827) (by native_decide) v.1 v.2
    ((@Law827.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 828 takes them (4 nodes). -/
def ordS11R173_Law828 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 828. -/
theorem noS11R173_Law828 : ∀ v : Magma.tup11R173,
    ¬ @Equation828 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law828) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law828) (by native_decide) v.1 v.2
    ((@Law828.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 829 takes them (3 nodes). -/
def ordS11R173_Law829 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 829. -/
theorem noS11R173_Law829 : ∀ v : Magma.tup11R173,
    ¬ @Equation829 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law829) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law829) (by native_decide) v.1 v.2
    ((@Law829.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 830 takes them (3 nodes). -/
def ordS11R173_Law830 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 830. -/
theorem noS11R173_Law830 : ∀ v : Magma.tup11R173,
    ¬ @Equation830 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law830) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law830) (by native_decide) v.1 v.2
    ((@Law830.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 831 takes them (3 nodes). -/
def ordS11R173_Law831 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 831. -/
theorem noS11R173_Law831 : ∀ v : Magma.tup11R173,
    ¬ @Equation831 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law831) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law831) (by native_decide) v.1 v.2
    ((@Law831.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 832 takes them (4 nodes). -/
def ordS11R173_Law832 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 832. -/
theorem noS11R173_Law832 : ∀ v : Magma.tup11R173,
    ¬ @Equation832 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law832) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law832) (by native_decide) v.1 v.2
    ((@Law832.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 833 takes them (3 nodes). -/
def ordS11R173_Law833 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 833. -/
theorem noS11R173_Law833 : ∀ v : Magma.tup11R173,
    ¬ @Equation833 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (3 nodes). -/
def ordS11R173_Law834 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 834. -/
theorem noS11R173_Law834 : ∀ v : Magma.tup11R173,
    ¬ @Equation834 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 835 takes them (4 nodes). -/
def ordS11R173_Law835 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 835. -/
theorem noS11R173_Law835 : ∀ v : Magma.tup11R173,
    ¬ @Equation835 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law835) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law835) (by native_decide) v.1 v.2
    ((@Law835.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (3 nodes). -/
def ordS11R173_Law836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 836. -/
theorem noS11R173_Law836 : ∀ v : Magma.tup11R173,
    ¬ @Equation836 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (3 nodes). -/
def ordS11R173_Law837 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 837. -/
theorem noS11R173_Law837 : ∀ v : Magma.tup11R173,
    ¬ @Equation837 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 838 takes them (4 nodes). -/
def ordS11R173_Law838 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 838. -/
theorem noS11R173_Law838 : ∀ v : Magma.tup11R173,
    ¬ @Equation838 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law838) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law838) (by native_decide) v.1 v.2
    ((@Law838.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 839 takes them (3 nodes). -/
def ordS11R173_Law839 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 839. -/
theorem noS11R173_Law839 : ∀ v : Magma.tup11R173,
    ¬ @Equation839 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law839) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law839) (by native_decide) v.1 v.2
    ((@Law839.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 842 takes them (4 nodes). -/
def ordS11R173_Law842 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 842. -/
theorem noS11R173_Law842 : ∀ v : Magma.tup11R173,
    ¬ @Equation842 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law842) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law842) (by native_decide) v.1 v.2
    ((@Law842.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (3 nodes). -/
def ordS11R173_Law843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 843. -/
theorem noS11R173_Law843 : ∀ v : Magma.tup11R173,
    ¬ @Equation843 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 848 takes them (4 nodes). -/
def ordS11R173_Law848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 848. -/
theorem noS11R173_Law848 : ∀ v : Magma.tup11R173,
    ¬ @Equation848 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law848) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law848) (by native_decide) v.1 v.2
    ((@Law848.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 852 takes them (4 nodes). -/
def ordS11R173_Law852 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 852. -/
theorem noS11R173_Law852 : ∀ v : Magma.tup11R173,
    ¬ @Equation852 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law852) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law852) (by native_decide) v.1 v.2
    ((@Law852.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 854 takes them (3 nodes). -/
def ordS11R173_Law854 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 854. -/
theorem noS11R173_Law854 : ∀ v : Magma.tup11R173,
    ¬ @Equation854 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law854) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law854) (by native_decide) v.1 v.2
    ((@Law854.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 856 takes them (4 nodes). -/
def ordS11R173_Law856 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 856. -/
theorem noS11R173_Law856 : ∀ v : Magma.tup11R173,
    ¬ @Equation856 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law856) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law856) (by native_decide) v.1 v.2
    ((@Law856.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 860 takes them (4 nodes). -/
def ordS11R173_Law860 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 860. -/
theorem noS11R173_Law860 : ∀ v : Magma.tup11R173,
    ¬ @Equation860 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law860) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law860) (by native_decide) v.1 v.2
    ((@Law860.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 864 takes them (4 nodes). -/
def ordS11R173_Law864 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 864. -/
theorem noS11R173_Law864 : ∀ v : Magma.tup11R173,
    ¬ @Equation864 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law864) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law864) (by native_decide) v.1 v.2
    ((@Law864.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 872 takes them (3 nodes). -/
def ordS11R173_Law872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 872. -/
theorem noS11R173_Law872 : ∀ v : Magma.tup11R173,
    ¬ @Equation872 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 879 takes them (3 nodes). -/
def ordS11R173_Law879 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 879. -/
theorem noS11R173_Law879 : ∀ v : Magma.tup11R173,
    ¬ @Equation879 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law879) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law879) (by native_decide) v.1 v.2
    ((@Law879.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (3 nodes). -/
def ordS11R173_Law919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 919. -/
theorem noS11R173_Law919 : ∀ v : Magma.tup11R173,
    ¬ @Equation919 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1021 takes them (3 nodes). -/
def ordS11R173_Law1021 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1021. -/
theorem noS11R173_Law1021 : ∀ v : Magma.tup11R173,
    ¬ @Equation1021 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1021) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1021) (by native_decide) v.1 v.2
    ((@Law1021.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1022 takes them (4 nodes). -/
def ordS11R173_Law1022 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1022. -/
theorem noS11R173_Law1022 : ∀ v : Magma.tup11R173,
    ¬ @Equation1022 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1022) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law1022) (by native_decide) v.1 v.2
    ((@Law1022.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1024 takes them (3 nodes). -/
def ordS11R173_Law1024 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1024. -/
theorem noS11R173_Law1024 : ∀ v : Magma.tup11R173,
    ¬ @Equation1024 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1024) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law1024) (by native_decide) v.1 v.2
    ((@Law1024.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_1 :
    FamilyRefutes Magma.srch11R173 [
      442, 446, 450, 454, 458, 463, 469, 473, 479, 483, 487, 491, 495, 506, 510, 516, 520, 524,
      532, 537, 541, 545, 549, 554, 558, 562, 566, 571, 579, 583, 588, 593, 598, 603, 615, 616,
      618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 632, 635, 645, 649, 653, 657,
      661, 679, 716, 818, 819, 820, 821, 822, 823, 824, 825, 827, 828, 829, 830, 831, 832, 833,
      834, 835, 836, 837, 838, 839, 842, 843, 848, 852, 854, 856, 860, 864, 872, 879, 919, 1021,
      1022, 1024
    ] :=
  ⟨noS11R173_Law442, noS11R173_Law446, noS11R173_Law450, noS11R173_Law454, noS11R173_Law458, noS11R173_Law463, noS11R173_Law469, noS11R173_Law473, noS11R173_Law479, noS11R173_Law483, noS11R173_Law487, noS11R173_Law491, noS11R173_Law495, noS11R173_Law506, noS11R173_Law510, noS11R173_Law516, noS11R173_Law520, noS11R173_Law524, noS11R173_Law532, noS11R173_Law537, noS11R173_Law541, noS11R173_Law545, noS11R173_Law549, noS11R173_Law554, noS11R173_Law558, noS11R173_Law562, noS11R173_Law566, noS11R173_Law571, noS11R173_Law579, noS11R173_Law583, noS11R173_Law588, noS11R173_Law593, noS11R173_Law598, noS11R173_Law603, noS11R173_Law615, noS11R173_Law616, noS11R173_Law618, noS11R173_Law619, noS11R173_Law620, noS11R173_Law621, noS11R173_Law622, noS11R173_Law623, noS11R173_Law624, noS11R173_Law625, noS11R173_Law626, noS11R173_Law627, noS11R173_Law628, noS11R173_Law629, noS11R173_Law632, noS11R173_Law635, noS11R173_Law645, noS11R173_Law649, noS11R173_Law653, noS11R173_Law657, noS11R173_Law661, noS11R173_Law679, noS11R173_Law716, noS11R173_Law818, noS11R173_Law819, noS11R173_Law820, noS11R173_Law821, noS11R173_Law822, noS11R173_Law823, noS11R173_Law824, noS11R173_Law825, noS11R173_Law827, noS11R173_Law828, noS11R173_Law829, noS11R173_Law830, noS11R173_Law831, noS11R173_Law832, noS11R173_Law833, noS11R173_Law834, noS11R173_Law835, noS11R173_Law836, noS11R173_Law837, noS11R173_Law838, noS11R173_Law839, noS11R173_Law842, noS11R173_Law843, noS11R173_Law848, noS11R173_Law852, noS11R173_Law854, noS11R173_Law856, noS11R173_Law860, noS11R173_Law864, noS11R173_Law872, noS11R173_Law879, noS11R173_Law919, noS11R173_Law1021, noS11R173_Law1022, noS11R173_Law1024⟩

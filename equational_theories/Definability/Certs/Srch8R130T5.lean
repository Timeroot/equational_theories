import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 6 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 299 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3461 takes them (4 nodes). -/
def ordS8R130_Law3461 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3461. -/
theorem noS8R130_Law3461 : ∀ v : Magma.tup8R130,
    ¬ @Equation3461 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3461) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3461) (by native_decide) v.1 v.2
    ((@Law3461.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (3 nodes). -/
def ordS8R130_Law3462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3462. -/
theorem noS8R130_Law3462 : ∀ v : Magma.tup8R130,
    ¬ @Equation3462 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3464 takes them (4 nodes). -/
def ordS8R130_Law3464 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3464. -/
theorem noS8R130_Law3464 : ∀ v : Magma.tup8R130,
    ¬ @Equation3464 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3464) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3464) (by native_decide) v.1 v.2
    ((@Law3464.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3465 takes them (3 nodes). -/
def ordS8R130_Law3465 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3465. -/
theorem noS8R130_Law3465 : ∀ v : Magma.tup8R130,
    ¬ @Equation3465 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3465) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3465) (by native_decide) v.1 v.2
    ((@Law3465.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3466 takes them (3 nodes). -/
def ordS8R130_Law3466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3466. -/
theorem noS8R130_Law3466 : ∀ v : Magma.tup8R130,
    ¬ @Equation3466 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3466) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3466) (by native_decide) v.1 v.2
    ((@Law3466.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3471 takes them (3 nodes). -/
def ordS8R130_Law3471 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3471. -/
theorem noS8R130_Law3471 : ∀ v : Magma.tup8R130,
    ¬ @Equation3471 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3471) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3471) (by native_decide) v.1 v.2
    ((@Law3471.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (3 nodes). -/
def ordS8R130_Law3474 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3474. -/
theorem noS8R130_Law3474 : ∀ v : Magma.tup8R130,
    ¬ @Equation3474 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (3 nodes). -/
def ordS8R130_Law3481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3481. -/
theorem noS8R130_Law3481 : ∀ v : Magma.tup8R130,
    ¬ @Equation3481 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (3 nodes). -/
def ordS8R130_Law3484 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3484. -/
theorem noS8R130_Law3484 : ∀ v : Magma.tup8R130,
    ¬ @Equation3484 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3499 takes them (3 nodes). -/
def ordS8R130_Law3499 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3499. -/
theorem noS8R130_Law3499 : ∀ v : Magma.tup8R130,
    ¬ @Equation3499 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3499) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3499) (by native_decide) v.1 v.2
    ((@Law3499.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3509 takes them (4 nodes). -/
def ordS8R130_Law3509 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3509. -/
theorem noS8R130_Law3509 : ∀ v : Magma.tup8R130,
    ¬ @Equation3509 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3509) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3509) (by native_decide) v.1 v.2
    ((@Law3509.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (3 nodes). -/
def ordS8R130_Law3511 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3511. -/
theorem noS8R130_Law3511 : ∀ v : Magma.tup8R130,
    ¬ @Equation3511 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3512 takes them (4 nodes). -/
def ordS8R130_Law3512 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3512. -/
theorem noS8R130_Law3512 : ∀ v : Magma.tup8R130,
    ¬ @Equation3512 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3512) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3512) (by native_decide) v.1 v.2
    ((@Law3512.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (3 nodes). -/
def ordS8R130_Law3518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3518. -/
theorem noS8R130_Law3518 : ∀ v : Magma.tup8R130,
    ¬ @Equation3518 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3519 takes them (4 nodes). -/
def ordS8R130_Law3519 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3519. -/
theorem noS8R130_Law3519 : ∀ v : Magma.tup8R130,
    ¬ @Equation3519 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3519) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3519) (by native_decide) v.1 v.2
    ((@Law3519.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (3 nodes). -/
def ordS8R130_Law3521 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3521. -/
theorem noS8R130_Law3521 : ∀ v : Magma.tup8R130,
    ¬ @Equation3521 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (3 nodes). -/
def ordS8R130_Law3526 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3526. -/
theorem noS8R130_Law3526 : ∀ v : Magma.tup8R130,
    ¬ @Equation3526 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3533 takes them (4 nodes). -/
def ordS8R130_Law3533 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3533. -/
theorem noS8R130_Law3533 : ∀ v : Magma.tup8R130,
    ¬ @Equation3533 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3533) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3533) (by native_decide) v.1 v.2
    ((@Law3533.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (3 nodes). -/
def ordS8R130_Law3534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3534. -/
theorem noS8R130_Law3534 : ∀ v : Magma.tup8R130,
    ¬ @Equation3534 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3537 takes them (4 nodes). -/
def ordS8R130_Law3537 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3537. -/
theorem noS8R130_Law3537 : ∀ v : Magma.tup8R130,
    ¬ @Equation3537 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3537) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3537) (by native_decide) v.1 v.2
    ((@Law3537.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3546 takes them (3 nodes). -/
def ordS8R130_Law3546 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3546. -/
theorem noS8R130_Law3546 : ∀ v : Magma.tup8R130,
    ¬ @Equation3546 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3546) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3546) (by native_decide) v.1 v.2
    ((@Law3546.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (3 nodes). -/
def ordS8R130_Law3549 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3549. -/
theorem noS8R130_Law3549 : ∀ v : Magma.tup8R130,
    ¬ @Equation3549 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (3 nodes). -/
def ordS8R130_Law3556 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3556. -/
theorem noS8R130_Law3556 : ∀ v : Magma.tup8R130,
    ¬ @Equation3556 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3591 takes them (3 nodes). -/
def ordS8R130_Law3591 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3591. -/
theorem noS8R130_Law3591 : ∀ v : Magma.tup8R130,
    ¬ @Equation3591 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3591) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3591) (by native_decide) v.1 v.2
    ((@Law3591.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3617 takes them (3 nodes). -/
def ordS8R130_Law3617 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3617. -/
theorem noS8R130_Law3617 : ∀ v : Magma.tup8R130,
    ¬ @Equation3617 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3617) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3617) (by native_decide) v.1 v.2
    ((@Law3617.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3660 takes them (3 nodes). -/
def ordS8R130_Law3660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3660. -/
theorem noS8R130_Law3660 : ∀ v : Magma.tup8R130,
    ¬ @Equation3660 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3660) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3660) (by native_decide) v.1 v.2
    ((@Law3660.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3661 takes them (4 nodes). -/
def ordS8R130_Law3661 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3661. -/
theorem noS8R130_Law3661 : ∀ v : Magma.tup8R130,
    ¬ @Equation3661 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3661) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3661) (by native_decide) v.1 v.2
    ((@Law3661.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3662 takes them (3 nodes). -/
def ordS8R130_Law3662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3662. -/
theorem noS8R130_Law3662 : ∀ v : Magma.tup8R130,
    ¬ @Equation3662 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3662) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3662) (by native_decide) v.1 v.2
    ((@Law3662.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3663 takes them (3 nodes). -/
def ordS8R130_Law3663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3663. -/
theorem noS8R130_Law3663 : ∀ v : Magma.tup8R130,
    ¬ @Equation3663 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3663) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3663) (by native_decide) v.1 v.2
    ((@Law3663.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3664 takes them (4 nodes). -/
def ordS8R130_Law3664 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3664. -/
theorem noS8R130_Law3664 : ∀ v : Magma.tup8R130,
    ¬ @Equation3664 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3664) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3664) (by native_decide) v.1 v.2
    ((@Law3664.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3665 takes them (3 nodes). -/
def ordS8R130_Law3665 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3665. -/
theorem noS8R130_Law3665 : ∀ v : Magma.tup8R130,
    ¬ @Equation3665 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3665) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3665) (by native_decide) v.1 v.2
    ((@Law3665.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (3 nodes). -/
def ordS8R130_Law3668 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3668. -/
theorem noS8R130_Law3668 : ∀ v : Magma.tup8R130,
    ¬ @Equation3668 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3672 takes them (3 nodes). -/
def ordS8R130_Law3672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3672. -/
theorem noS8R130_Law3672 : ∀ v : Magma.tup8R130,
    ¬ @Equation3672 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3672) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3672) (by native_decide) v.1 v.2
    ((@Law3672.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3674 takes them (3 nodes). -/
def ordS8R130_Law3674 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3674. -/
theorem noS8R130_Law3674 : ∀ v : Magma.tup8R130,
    ¬ @Equation3674 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3674) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3674) (by native_decide) v.1 v.2
    ((@Law3674.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3677 takes them (3 nodes). -/
def ordS8R130_Law3677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3677. -/
theorem noS8R130_Law3677 : ∀ v : Magma.tup8R130,
    ¬ @Equation3677 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3677) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3677) (by native_decide) v.1 v.2
    ((@Law3677.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3684 takes them (3 nodes). -/
def ordS8R130_Law3684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3684. -/
theorem noS8R130_Law3684 : ∀ v : Magma.tup8R130,
    ¬ @Equation3684 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3684) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3684) (by native_decide) v.1 v.2
    ((@Law3684.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (3 nodes). -/
def ordS8R130_Law3687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3687. -/
theorem noS8R130_Law3687 : ∀ v : Magma.tup8R130,
    ¬ @Equation3687 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3690 takes them (3 nodes). -/
def ordS8R130_Law3690 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3690. -/
theorem noS8R130_Law3690 : ∀ v : Magma.tup8R130,
    ¬ @Equation3690 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3690) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3690) (by native_decide) v.1 v.2
    ((@Law3690.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3694 takes them (3 nodes). -/
def ordS8R130_Law3694 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3694. -/
theorem noS8R130_Law3694 : ∀ v : Magma.tup8R130,
    ¬ @Equation3694 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3694) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3694) (by native_decide) v.1 v.2
    ((@Law3694.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3712 takes them (4 nodes). -/
def ordS8R130_Law3712 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3712. -/
theorem noS8R130_Law3712 : ∀ v : Magma.tup8R130,
    ¬ @Equation3712 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3712) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3712) (by native_decide) v.1 v.2
    ((@Law3712.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (3 nodes). -/
def ordS8R130_Law3714 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3714. -/
theorem noS8R130_Law3714 : ∀ v : Magma.tup8R130,
    ¬ @Equation3714 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3721 takes them (3 nodes). -/
def ordS8R130_Law3721 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3721. -/
theorem noS8R130_Law3721 : ∀ v : Magma.tup8R130,
    ¬ @Equation3721 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3721) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3721) (by native_decide) v.1 v.2
    ((@Law3721.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (3 nodes). -/
def ordS8R130_Law3724 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3724. -/
theorem noS8R130_Law3724 : ∀ v : Magma.tup8R130,
    ¬ @Equation3724 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3725 takes them (4 nodes). -/
def ordS8R130_Law3725 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3725. -/
theorem noS8R130_Law3725 : ∀ v : Magma.tup8R130,
    ¬ @Equation3725 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3725) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3725) (by native_decide) v.1 v.2
    ((@Law3725.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3729 takes them (3 nodes). -/
def ordS8R130_Law3729 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3729. -/
theorem noS8R130_Law3729 : ∀ v : Magma.tup8R130,
    ¬ @Equation3729 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3729) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3729) (by native_decide) v.1 v.2
    ((@Law3729.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3737 takes them (3 nodes). -/
def ordS8R130_Law3737 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3737. -/
theorem noS8R130_Law3737 : ∀ v : Magma.tup8R130,
    ¬ @Equation3737 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3737) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3737) (by native_decide) v.1 v.2
    ((@Law3737.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3740 takes them (4 nodes). -/
def ordS8R130_Law3740 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3740. -/
theorem noS8R130_Law3740 : ∀ v : Magma.tup8R130,
    ¬ @Equation3740 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3740) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3740) (by native_decide) v.1 v.2
    ((@Law3740.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (3 nodes). -/
def ordS8R130_Law3749 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3749. -/
theorem noS8R130_Law3749 : ∀ v : Magma.tup8R130,
    ¬ @Equation3749 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (3 nodes). -/
def ordS8R130_Law3752 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3752. -/
theorem noS8R130_Law3752 : ∀ v : Magma.tup8R130,
    ¬ @Equation3752 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3759 takes them (3 nodes). -/
def ordS8R130_Law3759 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3759. -/
theorem noS8R130_Law3759 : ∀ v : Magma.tup8R130,
    ¬ @Equation3759 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3759) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3759) (by native_decide) v.1 v.2
    ((@Law3759.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3794 takes them (3 nodes). -/
def ordS8R130_Law3794 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3794. -/
theorem noS8R130_Law3794 : ∀ v : Magma.tup8R130,
    ¬ @Equation3794 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3794) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3794) (by native_decide) v.1 v.2
    ((@Law3794.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3820 takes them (3 nodes). -/
def ordS8R130_Law3820 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3820. -/
theorem noS8R130_Law3820 : ∀ v : Magma.tup8R130,
    ¬ @Equation3820 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3820) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3820) (by native_decide) v.1 v.2
    ((@Law3820.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3863 takes them (3 nodes). -/
def ordS8R130_Law3863 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3863. -/
theorem noS8R130_Law3863 : ∀ v : Magma.tup8R130,
    ¬ @Equation3863 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3863) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3863) (by native_decide) v.1 v.2
    ((@Law3863.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3864 takes them (4 nodes). -/
def ordS8R130_Law3864 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3864. -/
theorem noS8R130_Law3864 : ∀ v : Magma.tup8R130,
    ¬ @Equation3864 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3864) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3864) (by native_decide) v.1 v.2
    ((@Law3864.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3865 takes them (3 nodes). -/
def ordS8R130_Law3865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3865. -/
theorem noS8R130_Law3865 : ∀ v : Magma.tup8R130,
    ¬ @Equation3865 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3867 takes them (4 nodes). -/
def ordS8R130_Law3867 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3867. -/
theorem noS8R130_Law3867 : ∀ v : Magma.tup8R130,
    ¬ @Equation3867 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3867) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3867) (by native_decide) v.1 v.2
    ((@Law3867.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3868 takes them (3 nodes). -/
def ordS8R130_Law3868 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3868. -/
theorem noS8R130_Law3868 : ∀ v : Magma.tup8R130,
    ¬ @Equation3868 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3870 takes them (4 nodes). -/
def ordS8R130_Law3870 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3870. -/
theorem noS8R130_Law3870 : ∀ v : Magma.tup8R130,
    ¬ @Equation3870 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3870) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3870) (by native_decide) v.1 v.2
    ((@Law3870.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (3 nodes). -/
def ordS8R130_Law3871 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3871. -/
theorem noS8R130_Law3871 : ∀ v : Magma.tup8R130,
    ¬ @Equation3871 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3872 takes them (3 nodes). -/
def ordS8R130_Law3872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3872. -/
theorem noS8R130_Law3872 : ∀ v : Magma.tup8R130,
    ¬ @Equation3872 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3872) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3872) (by native_decide) v.1 v.2
    ((@Law3872.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3877 takes them (3 nodes). -/
def ordS8R130_Law3877 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3877. -/
theorem noS8R130_Law3877 : ∀ v : Magma.tup8R130,
    ¬ @Equation3877 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3877) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3877) (by native_decide) v.1 v.2
    ((@Law3877.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (3 nodes). -/
def ordS8R130_Law3880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3880. -/
theorem noS8R130_Law3880 : ∀ v : Magma.tup8R130,
    ¬ @Equation3880 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (3 nodes). -/
def ordS8R130_Law3887 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3887. -/
theorem noS8R130_Law3887 : ∀ v : Magma.tup8R130,
    ¬ @Equation3887 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3890 takes them (3 nodes). -/
def ordS8R130_Law3890 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3890. -/
theorem noS8R130_Law3890 : ∀ v : Magma.tup8R130,
    ¬ @Equation3890 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3890) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3890) (by native_decide) v.1 v.2
    ((@Law3890.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3905 takes them (3 nodes). -/
def ordS8R130_Law3905 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3905. -/
theorem noS8R130_Law3905 : ∀ v : Magma.tup8R130,
    ¬ @Equation3905 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3905) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3905) (by native_decide) v.1 v.2
    ((@Law3905.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (3 nodes). -/
def ordS8R130_Law3917 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3917. -/
theorem noS8R130_Law3917 : ∀ v : Magma.tup8R130,
    ¬ @Equation3917 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3918 takes them (4 nodes). -/
def ordS8R130_Law3918 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3918. -/
theorem noS8R130_Law3918 : ∀ v : Magma.tup8R130,
    ¬ @Equation3918 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3918) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3918) (by native_decide) v.1 v.2
    ((@Law3918.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3921 takes them (4 nodes). -/
def ordS8R130_Law3921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3921. -/
theorem noS8R130_Law3921 : ∀ v : Magma.tup8R130,
    ¬ @Equation3921 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3921) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3921) (by native_decide) v.1 v.2
    ((@Law3921.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (3 nodes). -/
def ordS8R130_Law3924 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3924. -/
theorem noS8R130_Law3924 : ∀ v : Magma.tup8R130,
    ¬ @Equation3924 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3925 takes them (4 nodes). -/
def ordS8R130_Law3925 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3925. -/
theorem noS8R130_Law3925 : ∀ v : Magma.tup8R130,
    ¬ @Equation3925 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3925) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3925) (by native_decide) v.1 v.2
    ((@Law3925.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (3 nodes). -/
def ordS8R130_Law3927 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3927. -/
theorem noS8R130_Law3927 : ∀ v : Magma.tup8R130,
    ¬ @Equation3927 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3928 takes them (4 nodes). -/
def ordS8R130_Law3928 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3928. -/
theorem noS8R130_Law3928 : ∀ v : Magma.tup8R130,
    ¬ @Equation3928 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3928) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3928) (by native_decide) v.1 v.2
    ((@Law3928.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3932 takes them (3 nodes). -/
def ordS8R130_Law3932 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3932. -/
theorem noS8R130_Law3932 : ∀ v : Magma.tup8R130,
    ¬ @Equation3932 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3932) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3932) (by native_decide) v.1 v.2
    ((@Law3932.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3940 takes them (3 nodes). -/
def ordS8R130_Law3940 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3940. -/
theorem noS8R130_Law3940 : ∀ v : Magma.tup8R130,
    ¬ @Equation3940 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3940) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3940) (by native_decide) v.1 v.2
    ((@Law3940.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3943 takes them (4 nodes). -/
def ordS8R130_Law3943 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3943. -/
theorem noS8R130_Law3943 : ∀ v : Magma.tup8R130,
    ¬ @Equation3943 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3943) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3943) (by native_decide) v.1 v.2
    ((@Law3943.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (3 nodes). -/
def ordS8R130_Law3952 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3952. -/
theorem noS8R130_Law3952 : ∀ v : Magma.tup8R130,
    ¬ @Equation3952 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (3 nodes). -/
def ordS8R130_Law3955 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3955. -/
theorem noS8R130_Law3955 : ∀ v : Magma.tup8R130,
    ¬ @Equation3955 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (3 nodes). -/
def ordS8R130_Law3962 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3962. -/
theorem noS8R130_Law3962 : ∀ v : Magma.tup8R130,
    ¬ @Equation3962 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (3 nodes). -/
def ordS8R130_Law3997 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3997. -/
theorem noS8R130_Law3997 : ∀ v : Magma.tup8R130,
    ¬ @Equation3997 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (3 nodes). -/
def ordS8R130_Law4023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4023. -/
theorem noS8R130_Law4023 : ∀ v : Magma.tup8R130,
    ¬ @Equation4023 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4066 takes them (3 nodes). -/
def ordS8R130_Law4066 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4066. -/
theorem noS8R130_Law4066 : ∀ v : Magma.tup8R130,
    ¬ @Equation4066 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4066) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4066) (by native_decide) v.1 v.2
    ((@Law4066.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4067 takes them (4 nodes). -/
def ordS8R130_Law4067 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4067. -/
theorem noS8R130_Law4067 : ∀ v : Magma.tup8R130,
    ¬ @Equation4067 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4067) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4067) (by native_decide) v.1 v.2
    ((@Law4067.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (3 nodes). -/
def ordS8R130_Law4068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4068. -/
theorem noS8R130_Law4068 : ∀ v : Magma.tup8R130,
    ¬ @Equation4068 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4069 takes them (3 nodes). -/
def ordS8R130_Law4069 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4069. -/
theorem noS8R130_Law4069 : ∀ v : Magma.tup8R130,
    ¬ @Equation4069 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4069) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law4069) (by native_decide) v.1 v.2
    ((@Law4069.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4070 takes them (4 nodes). -/
def ordS8R130_Law4070 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4070. -/
theorem noS8R130_Law4070 : ∀ v : Magma.tup8R130,
    ¬ @Equation4070 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4070) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4070) (by native_decide) v.1 v.2
    ((@Law4070.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4071 takes them (3 nodes). -/
def ordS8R130_Law4071 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4071. -/
theorem noS8R130_Law4071 : ∀ v : Magma.tup8R130,
    ¬ @Equation4071 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4073 takes them (4 nodes). -/
def ordS8R130_Law4073 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4073. -/
theorem noS8R130_Law4073 : ∀ v : Magma.tup8R130,
    ¬ @Equation4073 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4073) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4073) (by native_decide) v.1 v.2
    ((@Law4073.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (3 nodes). -/
def ordS8R130_Law4074 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4074. -/
theorem noS8R130_Law4074 : ∀ v : Magma.tup8R130,
    ¬ @Equation4074 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4080 takes them (3 nodes). -/
def ordS8R130_Law4080 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4080. -/
theorem noS8R130_Law4080 : ∀ v : Magma.tup8R130,
    ¬ @Equation4080 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4080) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4080) (by native_decide) v.1 v.2
    ((@Law4080.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (3 nodes). -/
def ordS8R130_Law4083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4083. -/
theorem noS8R130_Law4083 : ∀ v : Magma.tup8R130,
    ¬ @Equation4083 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4090 takes them (3 nodes). -/
def ordS8R130_Law4090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4090. -/
theorem noS8R130_Law4090 : ∀ v : Magma.tup8R130,
    ¬ @Equation4090 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4090) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4090) (by native_decide) v.1 v.2
    ((@Law4090.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4093 takes them (3 nodes). -/
def ordS8R130_Law4093 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4093. -/
theorem noS8R130_Law4093 : ∀ v : Magma.tup8R130,
    ¬ @Equation4093 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4093) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law4093) (by native_decide) v.1 v.2
    ((@Law4093.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_5 :
    FamilyRefutes Magma.srch8R130 [
      3461, 3462, 3464, 3465, 3466, 3471, 3474, 3481, 3484, 3499, 3509, 3511, 3512, 3518, 3519,
      3521, 3526, 3533, 3534, 3537, 3546, 3549, 3556, 3591, 3617, 3660, 3661, 3662, 3663, 3664,
      3665, 3668, 3672, 3674, 3677, 3684, 3687, 3690, 3694, 3712, 3714, 3721, 3724, 3725, 3729,
      3737, 3740, 3749, 3752, 3759, 3794, 3820, 3863, 3864, 3865, 3867, 3868, 3870, 3871, 3872,
      3877, 3880, 3887, 3890, 3905, 3917, 3918, 3921, 3924, 3925, 3927, 3928, 3932, 3940, 3943,
      3952, 3955, 3962, 3997, 4023, 4066, 4067, 4068, 4069, 4070, 4071, 4073, 4074, 4080, 4083,
      4090, 4093
    ] :=
  ⟨noS8R130_Law3461, noS8R130_Law3462, noS8R130_Law3464, noS8R130_Law3465, noS8R130_Law3466, noS8R130_Law3471, noS8R130_Law3474, noS8R130_Law3481, noS8R130_Law3484, noS8R130_Law3499, noS8R130_Law3509, noS8R130_Law3511, noS8R130_Law3512, noS8R130_Law3518, noS8R130_Law3519, noS8R130_Law3521, noS8R130_Law3526, noS8R130_Law3533, noS8R130_Law3534, noS8R130_Law3537, noS8R130_Law3546, noS8R130_Law3549, noS8R130_Law3556, noS8R130_Law3591, noS8R130_Law3617, noS8R130_Law3660, noS8R130_Law3661, noS8R130_Law3662, noS8R130_Law3663, noS8R130_Law3664, noS8R130_Law3665, noS8R130_Law3668, noS8R130_Law3672, noS8R130_Law3674, noS8R130_Law3677, noS8R130_Law3684, noS8R130_Law3687, noS8R130_Law3690, noS8R130_Law3694, noS8R130_Law3712, noS8R130_Law3714, noS8R130_Law3721, noS8R130_Law3724, noS8R130_Law3725, noS8R130_Law3729, noS8R130_Law3737, noS8R130_Law3740, noS8R130_Law3749, noS8R130_Law3752, noS8R130_Law3759, noS8R130_Law3794, noS8R130_Law3820, noS8R130_Law3863, noS8R130_Law3864, noS8R130_Law3865, noS8R130_Law3867, noS8R130_Law3868, noS8R130_Law3870, noS8R130_Law3871, noS8R130_Law3872, noS8R130_Law3877, noS8R130_Law3880, noS8R130_Law3887, noS8R130_Law3890, noS8R130_Law3905, noS8R130_Law3917, noS8R130_Law3918, noS8R130_Law3921, noS8R130_Law3924, noS8R130_Law3925, noS8R130_Law3927, noS8R130_Law3928, noS8R130_Law3932, noS8R130_Law3940, noS8R130_Law3943, noS8R130_Law3952, noS8R130_Law3955, noS8R130_Law3962, noS8R130_Law3997, noS8R130_Law4023, noS8R130_Law4066, noS8R130_Law4067, noS8R130_Law4068, noS8R130_Law4069, noS8R130_Law4070, noS8R130_Law4071, noS8R130_Law4073, noS8R130_Law4074, noS8R130_Law4080, noS8R130_Law4083, noS8R130_Law4090, noS8R130_Law4093⟩

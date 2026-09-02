import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 199 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 3,093 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3517 takes them (153 nodes). -/
def ordS9R2000_Law3517 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3517. -/
theorem noS9R2000_Law3517 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3517 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3517) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3517) (by native_decide) v.1 v.2
    ((@Law3517.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3528 takes them (87 nodes). -/
def ordS9R2000_Law3528 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3528. -/
theorem noS9R2000_Law3528 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3528 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3528) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3528) (by native_decide) v.1 v.2
    ((@Law3528.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3530 takes them (87 nodes). -/
def ordS9R2000_Law3530 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3530. -/
theorem noS9R2000_Law3530 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3530 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3530) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3530) (by native_decide) v.1 v.2
    ((@Law3530.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3531 takes them (87 nodes). -/
def ordS9R2000_Law3531 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3531. -/
theorem noS9R2000_Law3531 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3531 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3531) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3531) (by native_decide) v.1 v.2
    ((@Law3531.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3536 takes them (87 nodes). -/
def ordS9R2000_Law3536 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3536. -/
theorem noS9R2000_Law3536 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3536 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3536) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3536) (by native_decide) v.1 v.2
    ((@Law3536.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3538 takes them (87 nodes). -/
def ordS9R2000_Law3538 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3538. -/
theorem noS9R2000_Law3538 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3538 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3538) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3538) (by native_decide) v.1 v.2
    ((@Law3538.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3539 takes them (87 nodes). -/
def ordS9R2000_Law3539 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3539. -/
theorem noS9R2000_Law3539 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3539 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3539) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3539) (by native_decide) v.1 v.2
    ((@Law3539.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3540 takes them (87 nodes). -/
def ordS9R2000_Law3540 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3540. -/
theorem noS9R2000_Law3540 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3540 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3540) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3540) (by native_decide) v.1 v.2
    ((@Law3540.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3542 takes them (87 nodes). -/
def ordS9R2000_Law3542 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3542. -/
theorem noS9R2000_Law3542 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3542 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3542) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3542) (by native_decide) v.1 v.2
    ((@Law3542.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3543 takes them (87 nodes). -/
def ordS9R2000_Law3543 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3543. -/
theorem noS9R2000_Law3543 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3543 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3543) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3543) (by native_decide) v.1 v.2
    ((@Law3543.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3544 takes them (87 nodes). -/
def ordS9R2000_Law3544 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3544. -/
theorem noS9R2000_Law3544 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3544 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3544) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law3544) (by native_decide) v.1 v.2
    ((@Law3544.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3595 takes them (55 nodes). -/
def ordS9R2000_Law3595 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3595. -/
theorem noS9R2000_Law3595 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3595 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3595) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3595) (by native_decide) v.1 v.2
    ((@Law3595.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3608 takes them (938 nodes). -/
def ordS9R2000_Law3608 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3608. -/
theorem noS9R2000_Law3608 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3608 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3608) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3608) (by native_decide) v.1 v.2
    ((@Law3608.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3612 takes them (938 nodes). -/
def ordS9R2000_Law3612 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3612. -/
theorem noS9R2000_Law3612 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3612 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3612) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3612) (by native_decide) v.1 v.2
    ((@Law3612.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3625 takes them (77 nodes). -/
def ordS9R2000_Law3625 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3625. -/
theorem noS9R2000_Law3625 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3625 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3625) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3625) (by native_decide) v.1 v.2
    ((@Law3625.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3629 takes them (62 nodes). -/
def ordS9R2000_Law3629 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3629. -/
theorem noS9R2000_Law3629 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3629 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3629) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3629) (by native_decide) v.1 v.2
    ((@Law3629.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch9R2000_refutes_198 :
    FamilyRefutes Magma.srch9R2000 [
      3517, 3528, 3530, 3531, 3536, 3538, 3539, 3540, 3542, 3543, 3544, 3595, 3608, 3612, 3625,
      3629
    ] :=
  ⟨noS9R2000_Law3517, noS9R2000_Law3528, noS9R2000_Law3530, noS9R2000_Law3531, noS9R2000_Law3536, noS9R2000_Law3538, noS9R2000_Law3539, noS9R2000_Law3540, noS9R2000_Law3542, noS9R2000_Law3543, noS9R2000_Law3544, noS9R2000_Law3595, noS9R2000_Law3608, noS9R2000_Law3612, noS9R2000_Law3625, noS9R2000_Law3629⟩

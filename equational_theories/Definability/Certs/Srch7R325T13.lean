import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 14 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 570 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4394 takes them (10 nodes). -/
def ordS7R325_Law4394 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4394. -/
theorem noS7R325_Law4394 : ∀ v : Magma.tup7R325,
    ¬ @Equation4394 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4394) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4394) (by native_decide) v.1 v.2
    ((@Law4394.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4474 takes them (205 nodes). -/
def ordS7R325_Law4474 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4474. -/
theorem noS7R325_Law4474 : ∀ v : Magma.tup7R325,
    ¬ @Equation4474 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4474) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4474) (by native_decide) v.1 v.2
    ((@Law4474.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4476 takes them (35 nodes). -/
def ordS7R325_Law4476 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4476. -/
theorem noS7R325_Law4476 : ∀ v : Magma.tup7R325,
    ¬ @Equation4476 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4476) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4476) (by native_decide) v.1 v.2
    ((@Law4476.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4478 takes them (17 nodes). -/
def ordS7R325_Law4478 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4478. -/
theorem noS7R325_Law4478 : ∀ v : Magma.tup7R325,
    ¬ @Equation4478 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4478) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4478) (by native_decide) v.1 v.2
    ((@Law4478.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4481 takes them (187 nodes). -/
def ordS7R325_Law4481 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4481. -/
theorem noS7R325_Law4481 : ∀ v : Magma.tup7R325,
    ¬ @Equation4481 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4481) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4481) (by native_decide) v.1 v.2
    ((@Law4481.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4485 takes them (16 nodes). -/
def ordS7R325_Law4485 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4485. -/
theorem noS7R325_Law4485 : ∀ v : Magma.tup7R325,
    ¬ @Equation4485 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4485) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4485) (by native_decide) v.1 v.2
    ((@Law4485.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4488 takes them (10 nodes). -/
def ordS7R325_Law4488 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4488. -/
theorem noS7R325_Law4488 : ∀ v : Magma.tup7R325,
    ¬ @Equation4488 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4488) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4488) (by native_decide) v.1 v.2
    ((@Law4488.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4492 takes them (10 nodes). -/
def ordS7R325_Law4492 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4492. -/
theorem noS7R325_Law4492 : ∀ v : Magma.tup7R325,
    ¬ @Equation4492 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4492) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4492) (by native_decide) v.1 v.2
    ((@Law4492.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4493 takes them (16 nodes). -/
def ordS7R325_Law4493 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4493. -/
theorem noS7R325_Law4493 : ∀ v : Magma.tup7R325,
    ¬ @Equation4493 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4493) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4493) (by native_decide) v.1 v.2
    ((@Law4493.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4496 takes them (10 nodes). -/
def ordS7R325_Law4496 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4496. -/
theorem noS7R325_Law4496 : ∀ v : Magma.tup7R325,
    ¬ @Equation4496 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4496) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4496) (by native_decide) v.1 v.2
    ((@Law4496.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4501 takes them (16 nodes). -/
def ordS7R325_Law4501 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4501. -/
theorem noS7R325_Law4501 : ∀ v : Magma.tup7R325,
    ¬ @Equation4501 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4501) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4501) (by native_decide) v.1 v.2
    ((@Law4501.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4502 takes them (28 nodes). -/
def ordS7R325_Law4502 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4502. -/
theorem noS7R325_Law4502 : ∀ v : Magma.tup7R325,
    ¬ @Equation4502 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4502) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4502) (by native_decide) v.1 v.2
    ((@Law4502.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4505 takes them (10 nodes). -/
def ordS7R325_Law4505 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4505. -/
theorem noS7R325_Law4505 : ∀ v : Magma.tup7R325,
    ¬ @Equation4505 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4505) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4505) (by native_decide) v.1 v.2
    ((@Law4505.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch7R325_refutes_13 :
    FamilyRefutes Magma.srch7R325 [
      4394, 4474, 4476, 4478, 4481, 4485, 4488, 4492, 4493, 4496, 4501, 4502, 4505
    ] :=
  ⟨noS7R325_Law4394, noS7R325_Law4474, noS7R325_Law4476, noS7R325_Law4478, noS7R325_Law4481, noS7R325_Law4485, noS7R325_Law4488, noS7R325_Law4492, noS7R325_Law4493, noS7R325_Law4496, noS7R325_Law4501, noS7R325_Law4502, noS7R325_Law4505⟩

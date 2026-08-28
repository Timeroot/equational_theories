import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 36 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 2,553 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3482 takes them (318 nodes). -/
def ordS7R12_Law3482 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3482. -/
theorem noS7R12_Law3482 : ∀ v : Magma.tup7R12,
    ¬ @Equation3482 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3482) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3482) (by native_decide) v.1 v.2
    ((@Law3482.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3483 takes them (98 nodes). -/
def ordS7R12_Law3483 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3483. -/
theorem noS7R12_Law3483 : ∀ v : Magma.tup7R12,
    ¬ @Equation3483 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3483) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3483) (by native_decide) v.1 v.2
    ((@Law3483.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3487 takes them (100 nodes). -/
def ordS7R12_Law3487 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3487. -/
theorem noS7R12_Law3487 : ∀ v : Magma.tup7R12,
    ¬ @Equation3487 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3487) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3487) (by native_decide) v.1 v.2
    ((@Law3487.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3488 takes them (268 nodes). -/
def ordS7R12_Law3488 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3488. -/
theorem noS7R12_Law3488 : ∀ v : Magma.tup7R12,
    ¬ @Equation3488 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3488) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3488) (by native_decide) v.1 v.2
    ((@Law3488.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3490 takes them (82 nodes). -/
def ordS7R12_Law3490 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3490. -/
theorem noS7R12_Law3490 : ∀ v : Magma.tup7R12,
    ¬ @Equation3490 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3490) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3490) (by native_decide) v.1 v.2
    ((@Law3490.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3492 takes them (156 nodes). -/
def ordS7R12_Law3492 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3492. -/
theorem noS7R12_Law3492 : ∀ v : Magma.tup7R12,
    ¬ @Equation3492 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3492) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3492) (by native_decide) v.1 v.2
    ((@Law3492.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3493 takes them (91 nodes). -/
def ordS7R12_Law3493 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3493. -/
theorem noS7R12_Law3493 : ∀ v : Magma.tup7R12,
    ¬ @Equation3493 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3493) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3493) (by native_decide) v.1 v.2
    ((@Law3493.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3504 takes them (147 nodes). -/
def ordS7R12_Law3504 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3504. -/
theorem noS7R12_Law3504 : ∀ v : Magma.tup7R12,
    ¬ @Equation3504 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3504) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3504) (by native_decide) v.1 v.2
    ((@Law3504.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3505 takes them (80 nodes). -/
def ordS7R12_Law3505 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3505. -/
theorem noS7R12_Law3505 : ∀ v : Magma.tup7R12,
    ¬ @Equation3505 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3505) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3505) (by native_decide) v.1 v.2
    ((@Law3505.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3513 takes them (50 nodes). -/
def ordS7R12_Law3513 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3513. -/
theorem noS7R12_Law3513 : ∀ v : Magma.tup7R12,
    ¬ @Equation3513 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3513) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3513) (by native_decide) v.1 v.2
    ((@Law3513.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3515 takes them (57 nodes). -/
def ordS7R12_Law3515 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3515. -/
theorem noS7R12_Law3515 : ∀ v : Magma.tup7R12,
    ¬ @Equation3515 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3515) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3515) (by native_decide) v.1 v.2
    ((@Law3515.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (952 nodes). -/
def ordS7R12_Law3518 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3518. -/
theorem noS7R12_Law3518 : ∀ v : Magma.tup7R12,
    ¬ @Equation3518 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (154 nodes). -/
def ordS7R12_Law3520 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3520. -/
theorem noS7R12_Law3520 : ∀ v : Magma.tup7R12,
    ¬ @Equation3520 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch7R12_refutes_35 :
    FamilyRefutes Magma.srch7R12 [
      3482, 3483, 3487, 3488, 3490, 3492, 3493, 3504, 3505, 3513, 3515, 3518, 3520
    ] :=
  ⟨noS7R12_Law3482, noS7R12_Law3483, noS7R12_Law3487, noS7R12_Law3488, noS7R12_Law3490, noS7R12_Law3492, noS7R12_Law3493, noS7R12_Law3504, noS7R12_Law3505, noS7R12_Law3513, noS7R12_Law3515, noS7R12_Law3518, noS7R12_Law3520⟩

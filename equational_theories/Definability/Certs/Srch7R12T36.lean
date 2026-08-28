import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 37 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 3,429 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3521 takes them (969 nodes). -/
def ordS7R12_Law3521 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3521. -/
theorem noS7R12_Law3521 : ∀ v : Magma.tup7R12,
    ¬ @Equation3521 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (590 nodes). -/
def ordS7R12_Law3523 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3523. -/
theorem noS7R12_Law3523 : ∀ v : Magma.tup7R12,
    ¬ @Equation3523 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (140 nodes). -/
def ordS7R12_Law3524 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3524. -/
theorem noS7R12_Law3524 : ∀ v : Magma.tup7R12,
    ¬ @Equation3524 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3525 takes them (322 nodes). -/
def ordS7R12_Law3525 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3525. -/
theorem noS7R12_Law3525 : ∀ v : Magma.tup7R12,
    ¬ @Equation3525 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3525) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3525) (by native_decide) v.1 v.2
    ((@Law3525.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (392 nodes). -/
def ordS7R12_Law3526 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3526. -/
theorem noS7R12_Law3526 : ∀ v : Magma.tup7R12,
    ¬ @Equation3526 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (80 nodes). -/
def ordS7R12_Law3527 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3527. -/
theorem noS7R12_Law3527 : ∀ v : Magma.tup7R12,
    ¬ @Equation3527 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (154 nodes). -/
def ordS7R12_Law3529 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3529. -/
theorem noS7R12_Law3529 : ∀ v : Magma.tup7R12,
    ¬ @Equation3529 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (117 nodes). -/
def ordS7R12_Law3534 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3534. -/
theorem noS7R12_Law3534 : ∀ v : Magma.tup7R12,
    ¬ @Equation3534 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3541 takes them (37 nodes). -/
def ordS7R12_Law3541 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3541. -/
theorem noS7R12_Law3541 : ∀ v : Magma.tup7R12,
    ¬ @Equation3541 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3541) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3541) (by native_decide) v.1 v.2
    ((@Law3541.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3545 takes them (628 nodes). -/
def ordS7R12_Law3545 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3545. -/
theorem noS7R12_Law3545 : ∀ v : Magma.tup7R12,
    ¬ @Equation3545 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3545) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3545) (by native_decide) v.1 v.2
    ((@Law3545.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch7R12_refutes_36 :
    FamilyRefutes Magma.srch7R12 [
      3521, 3523, 3524, 3525, 3526, 3527, 3529, 3534, 3541, 3545
    ] :=
  ⟨noS7R12_Law3521, noS7R12_Law3523, noS7R12_Law3524, noS7R12_Law3525, noS7R12_Law3526, noS7R12_Law3527, noS7R12_Law3529, noS7R12_Law3534, noS7R12_Law3541, noS7R12_Law3545⟩

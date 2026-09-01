import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 16 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,571 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4508 takes them (30 nodes). -/
def ordS7R325_Law4508 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4508. -/
theorem noS7R325_Law4508 : ∀ v : Magma.tup7R325,
    ¬ @Equation4508 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4508) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4508) (by native_decide) v.1 v.2
    ((@Law4508.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4509 takes them (22 nodes). -/
def ordS7R325_Law4509 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4509. -/
theorem noS7R325_Law4509 : ∀ v : Magma.tup7R325,
    ¬ @Equation4509 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4509) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4509) (by native_decide) v.1 v.2
    ((@Law4509.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4527 takes them (10 nodes). -/
def ordS7R325_Law4527 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4527. -/
theorem noS7R325_Law4527 : ∀ v : Magma.tup7R325,
    ¬ @Equation4527 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4527) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4527) (by native_decide) v.1 v.2
    ((@Law4527.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4528 takes them (3277 nodes). -/
def ordS7R325_Law4528 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4528. -/
theorem noS7R325_Law4528 : ∀ v : Magma.tup7R325,
    ¬ @Equation4528 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4528) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4528) (by native_decide) v.1 v.2
    ((@Law4528.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4529 takes them (206 nodes). -/
def ordS7R325_Law4529 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4529. -/
theorem noS7R325_Law4529 : ∀ v : Magma.tup7R325,
    ¬ @Equation4529 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4529) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4529) (by native_decide) v.1 v.2
    ((@Law4529.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4530 takes them (10 nodes). -/
def ordS7R325_Law4530 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4530. -/
theorem noS7R325_Law4530 : ∀ v : Magma.tup7R325,
    ¬ @Equation4530 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4530) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4530) (by native_decide) v.1 v.2
    ((@Law4530.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4548 takes them (16 nodes). -/
def ordS7R325_Law4548 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4548. -/
theorem noS7R325_Law4548 : ∀ v : Magma.tup7R325,
    ¬ @Equation4548 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4548) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4548) (by native_decide) v.1 v.2
    ((@Law4548.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch7R325_refutes_15 :
    FamilyRefutes Magma.srch7R325 [
      4508, 4509, 4527, 4528, 4529, 4530, 4548
    ] :=
  ⟨noS7R325_Law4508, noS7R325_Law4509, noS7R325_Law4527, noS7R325_Law4528, noS7R325_Law4529, noS7R325_Law4530, noS7R325_Law4548⟩

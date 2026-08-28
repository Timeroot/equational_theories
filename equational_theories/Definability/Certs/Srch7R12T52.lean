import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 53 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `15` equations here, 3,211 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4463 takes them (561 nodes). -/
def ordS7R12_Law4463 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4463. -/
theorem noS7R12_Law4463 : ∀ v : Magma.tup7R12,
    ¬ @Equation4463 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4463) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4463) (by native_decide) v.1 v.2
    ((@Law4463.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4466 takes them (57 nodes). -/
def ordS7R12_Law4466 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4466. -/
theorem noS7R12_Law4466 : ∀ v : Magma.tup7R12,
    ¬ @Equation4466 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4466) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4466) (by native_decide) v.1 v.2
    ((@Law4466.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4467 takes them (69 nodes). -/
def ordS7R12_Law4467 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4467. -/
theorem noS7R12_Law4467 : ∀ v : Magma.tup7R12,
    ¬ @Equation4467 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4467) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4467) (by native_decide) v.1 v.2
    ((@Law4467.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4472 takes them (376 nodes). -/
def ordS7R12_Law4472 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4472. -/
theorem noS7R12_Law4472 : ∀ v : Magma.tup7R12,
    ¬ @Equation4472 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4475 takes them (90 nodes). -/
def ordS7R12_Law4475 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4475. -/
theorem noS7R12_Law4475 : ∀ v : Magma.tup7R12,
    ¬ @Equation4475 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4475) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4475) (by native_decide) v.1 v.2
    ((@Law4475.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4480 takes them (413 nodes). -/
def ordS7R12_Law4480 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4480. -/
theorem noS7R12_Law4480 : ∀ v : Magma.tup7R12,
    ¬ @Equation4480 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4486 takes them (95 nodes). -/
def ordS7R12_Law4486 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4486. -/
theorem noS7R12_Law4486 : ∀ v : Magma.tup7R12,
    ¬ @Equation4486 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4486) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4486) (by native_decide) v.1 v.2
    ((@Law4486.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4490 takes them (97 nodes). -/
def ordS7R12_Law4490 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4490. -/
theorem noS7R12_Law4490 : ∀ v : Magma.tup7R12,
    ¬ @Equation4490 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4490) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4490) (by native_decide) v.1 v.2
    ((@Law4490.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4491 takes them (106 nodes). -/
def ordS7R12_Law4491 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4491. -/
theorem noS7R12_Law4491 : ∀ v : Magma.tup7R12,
    ¬ @Equation4491 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4491) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4491) (by native_decide) v.1 v.2
    ((@Law4491.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4495 takes them (91 nodes). -/
def ordS7R12_Law4495 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4495. -/
theorem noS7R12_Law4495 : ∀ v : Magma.tup7R12,
    ¬ @Equation4495 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4495) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4495) (by native_decide) v.1 v.2
    ((@Law4495.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4503 takes them (80 nodes). -/
def ordS7R12_Law4503 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4503. -/
theorem noS7R12_Law4503 : ∀ v : Magma.tup7R12,
    ¬ @Equation4503 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4503) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4503) (by native_decide) v.1 v.2
    ((@Law4503.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4507 takes them (555 nodes). -/
def ordS7R12_Law4507 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4507. -/
theorem noS7R12_Law4507 : ∀ v : Magma.tup7R12,
    ¬ @Equation4507 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4507) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4507) (by native_decide) v.1 v.2
    ((@Law4507.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4510 takes them (75 nodes). -/
def ordS7R12_Law4510 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4510. -/
theorem noS7R12_Law4510 : ∀ v : Magma.tup7R12,
    ¬ @Equation4510 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4510) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4510) (by native_decide) v.1 v.2
    ((@Law4510.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4531 takes them (268 nodes). -/
def ordS7R12_Law4531 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4531. -/
theorem noS7R12_Law4531 : ∀ v : Magma.tup7R12,
    ¬ @Equation4531 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4531) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4531) (by native_decide) v.1 v.2
    ((@Law4531.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4544 takes them (278 nodes). -/
def ordS7R12_Law4544 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4544. -/
theorem noS7R12_Law4544 : ∀ v : Magma.tup7R12,
    ¬ @Equation4544 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4544) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4544) (by native_decide) v.1 v.2
    ((@Law4544.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srch7R12_refutes_52 :
    FamilyRefutes Magma.srch7R12 [
      4463, 4466, 4467, 4472, 4475, 4480, 4486, 4490, 4491, 4495, 4503, 4507, 4510, 4531, 4544
    ] :=
  ⟨noS7R12_Law4463, noS7R12_Law4466, noS7R12_Law4467, noS7R12_Law4472, noS7R12_Law4475, noS7R12_Law4480, noS7R12_Law4486, noS7R12_Law4490, noS7R12_Law4491, noS7R12_Law4495, noS7R12_Law4503, noS7R12_Law4507, noS7R12_Law4510, noS7R12_Law4531, noS7R12_Law4544⟩

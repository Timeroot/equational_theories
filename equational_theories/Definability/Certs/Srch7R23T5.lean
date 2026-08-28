import equational_theories.Definability.Srch_S7R23

/-!
# Structural certificate targets: `Magma.srch7R23` (part 6 of 6)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R23_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `15` equations here, 2,842 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R23_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4515 takes them (608 nodes). -/
def ordS7R23_Law4515 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4515. -/
theorem noS7R23_Law4515 : ∀ v : Magma.tup7R23,
    ¬ @Equation4515 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4515) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4515) (by native_decide) v.1 v.2
    ((@Law4515.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4516 takes them (217 nodes). -/
def ordS7R23_Law4516 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4516. -/
theorem noS7R23_Law4516 : ∀ v : Magma.tup7R23,
    ¬ @Equation4516 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4516) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4516) (by native_decide) v.1 v.2
    ((@Law4516.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4517 takes them (56 nodes). -/
def ordS7R23_Law4517 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4517. -/
theorem noS7R23_Law4517 : ∀ v : Magma.tup7R23,
    ¬ @Equation4517 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4517) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4517) (by native_decide) v.1 v.2
    ((@Law4517.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4519 takes them (91 nodes). -/
def ordS7R23_Law4519 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4519. -/
theorem noS7R23_Law4519 : ∀ v : Magma.tup7R23,
    ¬ @Equation4519 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4519) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4519) (by native_decide) v.1 v.2
    ((@Law4519.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4520 takes them (95 nodes). -/
def ordS7R23_Law4520 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4520. -/
theorem noS7R23_Law4520 : ∀ v : Magma.tup7R23,
    ¬ @Equation4520 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4520) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4520) (by native_decide) v.1 v.2
    ((@Law4520.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4521 takes them (77 nodes). -/
def ordS7R23_Law4521 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4521. -/
theorem noS7R23_Law4521 : ∀ v : Magma.tup7R23,
    ¬ @Equation4521 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4521) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4521) (by native_decide) v.1 v.2
    ((@Law4521.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4522 takes them (43 nodes). -/
def ordS7R23_Law4522 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4522. -/
theorem noS7R23_Law4522 : ∀ v : Magma.tup7R23,
    ¬ @Equation4522 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4522) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 5)
    (ord := ordS7R23_Law4522) (by native_decide) v.1 v.2
    ((@Law4522.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4525 takes them (539 nodes). -/
def ordS7R23_Law4525 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4525. -/
theorem noS7R23_Law4525 : ∀ v : Magma.tup7R23,
    ¬ @Equation4525 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4525) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4525) (by native_decide) v.1 v.2
    ((@Law4525.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4533 takes them (124 nodes). -/
def ordS7R23_Law4533 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4533. -/
theorem noS7R23_Law4533 : ∀ v : Magma.tup7R23,
    ¬ @Equation4533 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4533) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4533) (by native_decide) v.1 v.2
    ((@Law4533.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4537 takes them (60 nodes). -/
def ordS7R23_Law4537 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4537. -/
theorem noS7R23_Law4537 : ∀ v : Magma.tup7R23,
    ¬ @Equation4537 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4537) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4537) (by native_decide) v.1 v.2
    ((@Law4537.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4541 takes them (433 nodes). -/
def ordS7R23_Law4541 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4541. -/
theorem noS7R23_Law4541 : ∀ v : Magma.tup7R23,
    ¬ @Equation4541 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4541) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4541) (by native_decide) v.1 v.2
    ((@Law4541.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4559 takes them (177 nodes). -/
def ordS7R23_Law4559 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4559. -/
theorem noS7R23_Law4559 : ∀ v : Magma.tup7R23,
    ¬ @Equation4559 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4559) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4559) (by native_decide) v.1 v.2
    ((@Law4559.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4564 takes them (210 nodes). -/
def ordS7R23_Law4564 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4564. -/
theorem noS7R23_Law4564 : ∀ v : Magma.tup7R23,
    ¬ @Equation4564 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4564) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4564) (by native_decide) v.1 v.2
    ((@Law4564.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4569 takes them (65 nodes). -/
def ordS7R23_Law4569 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4569. -/
theorem noS7R23_Law4569 : ∀ v : Magma.tup7R23,
    ¬ @Equation4569 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4569) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4569) (by native_decide) v.1 v.2
    ((@Law4569.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4579 takes them (47 nodes). -/
def ordS7R23_Law4579 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4579. -/
theorem noS7R23_Law4579 : ∀ v : Magma.tup7R23,
    ¬ @Equation4579 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4579) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 5)
    (ord := ordS7R23_Law4579) (by native_decide) v.1 v.2
    ((@Law4579.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srch7R23_refutes_5 :
    FamilyRefutes Magma.srch7R23 [
      4515, 4516, 4517, 4519, 4520, 4521, 4522, 4525, 4533, 4537, 4541, 4559, 4564, 4569, 4579
    ] :=
  ⟨noS7R23_Law4515, noS7R23_Law4516, noS7R23_Law4517, noS7R23_Law4519, noS7R23_Law4520, noS7R23_Law4521, noS7R23_Law4522, noS7R23_Law4525, noS7R23_Law4533, noS7R23_Law4537, noS7R23_Law4541, noS7R23_Law4559, noS7R23_Law4564, noS7R23_Law4569, noS7R23_Law4579⟩

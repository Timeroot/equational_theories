import equational_theories.Definability.Srch_S9R302

/-!
# Structural certificate targets: `Magma.srch9R302` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R302_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 482 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R302_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4386 takes them (65 nodes). -/
def ordS9R302_Law4386 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4386. -/
theorem noS9R302_Law4386 : ∀ v : Magma.tup9R302,
    ¬ @Equation4386 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4386) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law4386) (by native_decide) v.1 v.2
    ((@Law4386.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4413 takes them (19 nodes). -/
def ordS9R302_Law4413 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4413. -/
theorem noS9R302_Law4413 : ∀ v : Magma.tup9R302,
    ¬ @Equation4413 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4413) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4413) (by native_decide) v.1 v.2
    ((@Law4413.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4421 takes them (40 nodes). -/
def ordS9R302_Law4421 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4421. -/
theorem noS9R302_Law4421 : ∀ v : Magma.tup9R302,
    ¬ @Equation4421 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4421) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4421) (by native_decide) v.1 v.2
    ((@Law4421.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4446 takes them (126 nodes). -/
def ordS9R302_Law4446 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4446. -/
theorem noS9R302_Law4446 : ∀ v : Magma.tup9R302,
    ¬ @Equation4446 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4446) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 2)
    (ord := ordS9R302_Law4446) (by native_decide) v.1 v.2
    ((@Law4446.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4450 takes them (36 nodes). -/
def ordS9R302_Law4450 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4450. -/
theorem noS9R302_Law4450 : ∀ v : Magma.tup9R302,
    ¬ @Equation4450 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4450) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4450) (by native_decide) v.1 v.2
    ((@Law4450.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4458 takes them (23 nodes). -/
def ordS9R302_Law4458 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4458. -/
theorem noS9R302_Law4458 : ∀ v : Magma.tup9R302,
    ¬ @Equation4458 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4458) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4458) (by native_decide) v.1 v.2
    ((@Law4458.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4461 takes them (107 nodes). -/
def ordS9R302_Law4461 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4461. -/
theorem noS9R302_Law4461 : ∀ v : Magma.tup9R302,
    ¬ @Equation4461 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4461) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4461) (by native_decide) v.1 v.2
    ((@Law4461.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4491 takes them (33 nodes). -/
def ordS9R302_Law4491 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4491. -/
theorem noS9R302_Law4491 : ∀ v : Magma.tup9R302,
    ¬ @Equation4491 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4491) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4491) (by native_decide) v.1 v.2
    ((@Law4491.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4640 takes them (33 nodes). -/
def ordS9R302_Law4640 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4640. -/
theorem noS9R302_Law4640 : ∀ v : Magma.tup9R302,
    ¬ @Equation4640 (Fin 9) (Magma.srch9R302 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4640) (E := S9R302.E) (tr := S9R302.tr) (z := S9R302.z)
    (st := S9R302.st) (X := S9R302.X) (envs := Magma.envsRed 9 S9R302.E 3)
    (ord := ordS9R302_Law4640) (by native_decide) v.1 v.2
    ((@Law4640.models_iff (Fin 9) (Magma.srch9R302 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch9R302_refutes_1 :
    FamilyRefutes Magma.srch9R302 [
      4386, 4413, 4421, 4446, 4450, 4458, 4461, 4491, 4640
    ] :=
  ⟨noS9R302_Law4386, noS9R302_Law4413, noS9R302_Law4421, noS9R302_Law4446, noS9R302_Law4450, noS9R302_Law4458, noS9R302_Law4461, noS9R302_Law4491, noS9R302_Law4640⟩

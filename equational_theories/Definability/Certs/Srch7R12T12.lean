import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 13 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,357 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1437 takes them (687 nodes). -/
def ordS7R12_Law1437 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1437. -/
theorem noS7R12_Law1437 : ∀ v : Magma.tup7R12,
    ¬ @Equation1437 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1437) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1437) (by native_decide) v.1 v.2
    ((@Law1437.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1441 takes them (272 nodes). -/
def ordS7R12_Law1441 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1441. -/
theorem noS7R12_Law1441 : ∀ v : Magma.tup7R12,
    ¬ @Equation1441 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1441) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1441) (by native_decide) v.1 v.2
    ((@Law1441.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (325 nodes). -/
def ordS7R12_Law1442 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1442. -/
theorem noS7R12_Law1442 : ∀ v : Magma.tup7R12,
    ¬ @Equation1442 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (409 nodes). -/
def ordS7R12_Law1444 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1444. -/
theorem noS7R12_Law1444 : ∀ v : Magma.tup7R12,
    ¬ @Equation1444 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1451 takes them (619 nodes). -/
def ordS7R12_Law1451 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1451. -/
theorem noS7R12_Law1451 : ∀ v : Magma.tup7R12,
    ¬ @Equation1451 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1451) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1451) (by native_decide) v.1 v.2
    ((@Law1451.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1454 takes them (469 nodes). -/
def ordS7R12_Law1454 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1454. -/
theorem noS7R12_Law1454 : ∀ v : Magma.tup7R12,
    ¬ @Equation1454 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1454) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1454) (by native_decide) v.1 v.2
    ((@Law1454.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (363 nodes). -/
def ordS7R12_Law1455 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1455. -/
theorem noS7R12_Law1455 : ∀ v : Magma.tup7R12,
    ¬ @Equation1455 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1459 takes them (213 nodes). -/
def ordS7R12_Law1459 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1459. -/
theorem noS7R12_Law1459 : ∀ v : Magma.tup7R12,
    ¬ @Equation1459 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1459) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1459) (by native_decide) v.1 v.2
    ((@Law1459.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch7R12_refutes_12 :
    FamilyRefutes Magma.srch7R12 [
      1437, 1441, 1442, 1444, 1451, 1454, 1455, 1459
    ] :=
  ⟨noS7R12_Law1437, noS7R12_Law1441, noS7R12_Law1442, noS7R12_Law1444, noS7R12_Law1451, noS7R12_Law1454, noS7R12_Law1455, noS7R12_Law1459⟩

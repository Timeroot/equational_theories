import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 199 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,367 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3468 takes them (769 nodes). -/
def ordS8R9_Law3468 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3468. -/
theorem noS8R9_Law3468 : ∀ v : Magma.tup8R9,
    ¬ @Equation3468 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3469 takes them (776 nodes). -/
def ordS8R9_Law3469 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3469. -/
theorem noS8R9_Law3469 : ∀ v : Magma.tup8R9,
    ¬ @Equation3469 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3469) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3469) (by native_decide) v.1 v.2
    ((@Law3469.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3470 takes them (65 nodes). -/
def ordS8R9_Law3470 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3470. -/
theorem noS8R9_Law3470 : ∀ v : Magma.tup8R9,
    ¬ @Equation3470 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3470) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3470) (by native_decide) v.1 v.2
    ((@Law3470.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3477 takes them (741 nodes). -/
def ordS8R9_Law3477 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3477. -/
theorem noS8R9_Law3477 : ∀ v : Magma.tup8R9,
    ¬ @Equation3477 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3477) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3477) (by native_decide) v.1 v.2
    ((@Law3477.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3487 takes them (31 nodes). -/
def ordS8R9_Law3487 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3487. -/
theorem noS8R9_Law3487 : ∀ v : Magma.tup8R9,
    ¬ @Equation3487 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3487) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3487) (by native_decide) v.1 v.2
    ((@Law3487.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3491 takes them (741 nodes). -/
def ordS8R9_Law3491 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3491. -/
theorem noS8R9_Law3491 : ∀ v : Magma.tup8R9,
    ¬ @Equation3491 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3491) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3491) (by native_decide) v.1 v.2
    ((@Law3491.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3495 takes them (103 nodes). -/
def ordS8R9_Law3495 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3495. -/
theorem noS8R9_Law3495 : ∀ v : Magma.tup8R9,
    ¬ @Equation3495 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3495) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3495) (by native_decide) v.1 v.2
    ((@Law3495.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3499 takes them (9 nodes). -/
def ordS8R9_Law3499 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3499. -/
theorem noS8R9_Law3499 : ∀ v : Magma.tup8R9,
    ¬ @Equation3499 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3499) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3499) (by native_decide) v.1 v.2
    ((@Law3499.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3503 takes them (9 nodes). -/
def ordS8R9_Law3503 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3503. -/
theorem noS8R9_Law3503 : ∀ v : Magma.tup8R9,
    ¬ @Equation3503 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3503) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3503) (by native_decide) v.1 v.2
    ((@Law3503.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3510 takes them (123 nodes). -/
def ordS8R9_Law3510 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3510. -/
theorem noS8R9_Law3510 : ∀ v : Magma.tup8R9,
    ¬ @Equation3510 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3510) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3510) (by native_decide) v.1 v.2
    ((@Law3510.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch8R9_refutes_198 :
    FamilyRefutes Magma.srch8R9 [
      3468, 3469, 3470, 3477, 3487, 3491, 3495, 3499, 3503, 3510
    ] :=
  ⟨noS8R9_Law3468, noS8R9_Law3469, noS8R9_Law3470, noS8R9_Law3477, noS8R9_Law3487, noS8R9_Law3491, noS8R9_Law3495, noS8R9_Law3499, noS8R9_Law3503, noS8R9_Law3510⟩

import equational_theories.Definability.Srch_S8R40

/-!
# Structural certificate targets: `Magma.srch8R40` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R40_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `18` equations here, 3,086 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R40_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4452 takes them (273 nodes). -/
def ordS8R40_Law4452 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4452. -/
theorem noS8R40_Law4452 : ∀ v : Magma.tup8R40,
    ¬ @Equation4452 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4460 takes them (242 nodes). -/
def ordS8R40_Law4460 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4460. -/
theorem noS8R40_Law4460 : ∀ v : Magma.tup8R40,
    ¬ @Equation4460 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4460) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4460) (by native_decide) v.1 v.2
    ((@Law4460.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4464 takes them (87 nodes). -/
def ordS8R40_Law4464 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4464. -/
theorem noS8R40_Law4464 : ∀ v : Magma.tup8R40,
    ¬ @Equation4464 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4464) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4464) (by native_decide) v.1 v.2
    ((@Law4464.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4475 takes them (90 nodes). -/
def ordS8R40_Law4475 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4475. -/
theorem noS8R40_Law4475 : ∀ v : Magma.tup8R40,
    ¬ @Equation4475 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4475) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4475) (by native_decide) v.1 v.2
    ((@Law4475.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4478 takes them (39 nodes). -/
def ordS8R40_Law4478 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4478. -/
theorem noS8R40_Law4478 : ∀ v : Magma.tup8R40,
    ¬ @Equation4478 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4478) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4478) (by native_decide) v.1 v.2
    ((@Law4478.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4511 takes them (144 nodes). -/
def ordS8R40_Law4511 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4511. -/
theorem noS8R40_Law4511 : ∀ v : Magma.tup8R40,
    ¬ @Equation4511 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4511) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4511) (by native_decide) v.1 v.2
    ((@Law4511.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4514 takes them (85 nodes). -/
def ordS8R40_Law4514 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4514. -/
theorem noS8R40_Law4514 : ∀ v : Magma.tup8R40,
    ¬ @Equation4514 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4514) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4514) (by native_decide) v.1 v.2
    ((@Law4514.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4516 takes them (110 nodes). -/
def ordS8R40_Law4516 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4516. -/
theorem noS8R40_Law4516 : ∀ v : Magma.tup8R40,
    ¬ @Equation4516 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4516) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4516) (by native_decide) v.1 v.2
    ((@Law4516.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4518 takes them (51 nodes). -/
def ordS8R40_Law4518 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4518. -/
theorem noS8R40_Law4518 : ∀ v : Magma.tup8R40,
    ¬ @Equation4518 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4518) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4518) (by native_decide) v.1 v.2
    ((@Law4518.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4542 takes them (160 nodes). -/
def ordS8R40_Law4542 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4542. -/
theorem noS8R40_Law4542 : ∀ v : Magma.tup8R40,
    ¬ @Equation4542 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4542) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4542) (by native_decide) v.1 v.2
    ((@Law4542.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4550 takes them (195 nodes). -/
def ordS8R40_Law4550 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4550. -/
theorem noS8R40_Law4550 : ∀ v : Magma.tup8R40,
    ¬ @Equation4550 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4550) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4550) (by native_decide) v.1 v.2
    ((@Law4550.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4554 takes them (56 nodes). -/
def ordS8R40_Law4554 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4554. -/
theorem noS8R40_Law4554 : ∀ v : Magma.tup8R40,
    ¬ @Equation4554 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4554) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4554) (by native_decide) v.1 v.2
    ((@Law4554.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4574 takes them (167 nodes). -/
def ordS8R40_Law4574 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4574. -/
theorem noS8R40_Law4574 : ∀ v : Magma.tup8R40,
    ¬ @Equation4574 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4574) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4574) (by native_decide) v.1 v.2
    ((@Law4574.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4586 takes them (168 nodes). -/
def ordS8R40_Law4586 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4586. -/
theorem noS8R40_Law4586 : ∀ v : Magma.tup8R40,
    ¬ @Equation4586 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4586) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4586) (by native_decide) v.1 v.2
    ((@Law4586.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4600 takes them (492 nodes). -/
def ordS8R40_Law4600 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4600. -/
theorem noS8R40_Law4600 : ∀ v : Magma.tup8R40,
    ¬ @Equation4600 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4600) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4600) (by native_decide) v.1 v.2
    ((@Law4600.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4601 takes them (331 nodes). -/
def ordS8R40_Law4601 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4601. -/
theorem noS8R40_Law4601 : ∀ v : Magma.tup8R40,
    ¬ @Equation4601 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4601) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4601) (by native_decide) v.1 v.2
    ((@Law4601.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4603 takes them (228 nodes). -/
def ordS8R40_Law4603 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4603. -/
theorem noS8R40_Law4603 : ∀ v : Magma.tup8R40,
    ¬ @Equation4603 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4603) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4603) (by native_decide) v.1 v.2
    ((@Law4603.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4604 takes them (168 nodes). -/
def ordS8R40_Law4604 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4604. -/
theorem noS8R40_Law4604 : ∀ v : Magma.tup8R40,
    ¬ @Equation4604 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4604) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4604) (by native_decide) v.1 v.2
    ((@Law4604.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- No member of the class satisfies any of these `18` equations. -/
theorem srch8R40_refutes_3 :
    FamilyRefutes Magma.srch8R40 [
      4452, 4460, 4464, 4475, 4478, 4511, 4514, 4516, 4518, 4542, 4550, 4554, 4574, 4586, 4600,
      4601, 4603, 4604
    ] :=
  ⟨noS8R40_Law4452, noS8R40_Law4460, noS8R40_Law4464, noS8R40_Law4475, noS8R40_Law4478, noS8R40_Law4511, noS8R40_Law4514, noS8R40_Law4516, noS8R40_Law4518, noS8R40_Law4542, noS8R40_Law4550, noS8R40_Law4554, noS8R40_Law4574, noS8R40_Law4586, noS8R40_Law4600, noS8R40_Law4601, noS8R40_Law4603, noS8R40_Law4604⟩
